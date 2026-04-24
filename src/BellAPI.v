From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.
From BellStaging Require Import BellWitnesses.
From BellStaging Require Import BellSerialization.
From BellStaging Require Import BellCalibration.

Import ListNotations.
Open Scope string_scope.

Module API.

(* Canonical public entry points. Each function gates on domain
   validity and/or calibration status. Internal unvalidated primitives
   (Classification.classify, DifferentialDiagnosis.most_likely_diagnosis)
   remain in their own modules for proofs but should not be consumed
   by downstream code directly. *)

(* Primary classifier: validates domain then runs the permissive
   Walsh-Kliegman encoding. Returns None on out-of-domain input. *)
Definition classify (c : ClinicalState.t) : option Stage.t :=
  Classification.classify_validated c.

(* Strict-Bell classifier: same validation, Bell-strict IIA/IIB semantics. *)
Definition classify_strict (c : ClinicalState.t) : option Stage.t :=
  if ClinicalState.is_valid c
  then Some (Classification.classify_strict_bell c)
  else None.

(* Diagnosis: validates domain then runs the classifier + differential. *)
Definition diagnose (c : ClinicalState.t) : option Diagnosis.t :=
  if ClinicalState.is_valid c
  then Some (Classification.diagnose c)
  else None.

(* Differential diagnosis with mandatory calibration gate. *)
Definition differential (m : Calibration.CalibrationMetadata)
    (f : DifferentialDiagnosis.DifferentialFeatures)
    : option DifferentialDiagnosis.GIDifferential :=
  Calibration.diagnose_with_calibration m f.

(* Treatment selector from a validated stage. *)
Definition treatment (c : ClinicalState.t) : option Treatment.t :=
  match classify c with
  | Some s => Some (Treatment.of_stage s)
  | None => None
  end.

(* Surgery indicator from a validated state. *)
Definition requires_surgery (c : ClinicalState.t) : option bool :=
  match classify c with
  | Some s => Some (Treatment.requires_surgery (Treatment.of_stage s))
  | None => None
  end.

(* FHIR-shaped output of a validated classification. *)
Definition classify_fhir (c : ClinicalState.t) : option Serialization.JValue :=
  match classify c with
  | Some s => Some (Serialization.ser_stage_fhir s)
  | None => None
  end.

(* Audit entry creation gated on validity. *)
Definition audit (ts : nat) (c : ClinicalState.t)
    : option (nat * nat * bool) :=
  match classify c with
  | Some s => Some (ts, Stage.to_nat s,
                    Treatment.requires_surgery (Treatment.of_stage s))
  | None => None
  end.

(* --- API guarantees --- *)

Lemma api_classify_sound : forall c s,
  classify c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify in H.
  apply Classification.classify_validated_some_iff_valid in H. exact H.
Qed.

Lemma api_classify_agrees : forall c,
  ClinicalState.valid c ->
  classify c = Some (Classification.classify c).
Proof.
  intros c Hv. unfold classify.
  apply Classification.classify_validated_agrees_on_valid. exact Hv.
Qed.

Lemma api_strict_sound : forall c s,
  classify_strict c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify_strict in H.
  destruct (ClinicalState.is_valid c) eqn:E; [|discriminate].
  apply ClinicalState.is_valid_iff. exact E.
Qed.

Lemma api_diagnose_sound : forall c d,
  diagnose c = Some d -> ClinicalState.valid c.
Proof.
  intros c d H. unfold diagnose in H.
  destruct (ClinicalState.is_valid c) eqn:E; [|discriminate].
  apply ClinicalState.is_valid_iff. exact E.
Qed.

Lemma api_differential_requires_calibration : forall m f d,
  differential m f = Some d ->
  Calibration.is_calibrated m = true.
Proof.
  intros m f d H. unfold differential, Calibration.diagnose_with_calibration in H.
  destruct (Calibration.is_calibrated m) eqn:E; [reflexivity | discriminate].
Qed.

Lemma api_treatment_sound : forall c t,
  treatment c = Some t -> ClinicalState.valid c.
Proof.
  intros c t H. unfold treatment in H.
  destruct (classify c) as [s|] eqn:Hc; [|discriminate].
  apply api_classify_sound with (s := s). exact Hc.
Qed.

Lemma api_requires_surgery_sound : forall c b,
  requires_surgery c = Some b -> ClinicalState.valid c.
Proof.
  intros c b H. unfold requires_surgery in H.
  destruct (classify c) as [s|] eqn:Hc; [|discriminate].
  apply api_classify_sound with (s := s). exact Hc.
Qed.

Lemma api_requires_surgery_iff_IIIB : forall c,
  ClinicalState.valid c ->
  (requires_surgery c = Some true <->
   RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true).
Proof.
  intros c Hv. split.
  - intro H. unfold requires_surgery in H.
    rewrite (api_classify_agrees c Hv) in H.
    injection H as Hsurg.
    apply SafetyProperties.surgery_only_at_IIIB in Hsurg.
    unfold Classification.classify, Classification.classify_stage in Hsurg.
    destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c))
      eqn:E; [reflexivity|].
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _)%bool; try discriminate.
    destruct (_ && _)%bool; discriminate.
  - intro H. unfold requires_surgery.
    rewrite (api_classify_agrees c Hv).
    rewrite (Classification.pneumoperitoneum_forces_IIIB c H).
    reflexivity.
Qed.

Lemma api_audit_sound : forall ts c e,
  audit ts c = Some e -> ClinicalState.valid c.
Proof.
  intros ts c e H. unfold audit in H.
  destruct (classify c) as [s|] eqn:Hc; [|discriminate].
  apply api_classify_sound with (s := s). exact Hc.
Qed.

End API.
