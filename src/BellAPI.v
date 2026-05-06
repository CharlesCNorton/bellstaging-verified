From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.
From BellStaging Require Import BellCriteriaDecl.
From BellStaging Require Import BellWitnesses.
From BellStaging Require Import BellSerialization.
From BellStaging Require Import BellCalibration.

Import ListNotations.
Open Scope string_scope.

Module API.

(* Canonical public entry points. Each function gates on domain
   validity, staleness, and/or calibration status. Internal unvalidated
   primitives (Classification.classify, DifferentialDiagnosis.most_likely_diagnosis)
   remain in their own modules for proofs but should not be consumed
   by downstream code directly. *)

(* Production-readiness predicate: input is in-domain AND signs are fresh.
   Both conditions are required for routine clinical classification.
   The earlier API gated only on validity; the staleness machinery
   (signs_current, classify_checked) existed but was opt-in — making
   stale data the production default. This predicate flips the default. *)
Definition is_production_ready (c : ClinicalState.t) : bool :=
  ClinicalState.is_valid c && ClinicalState.signs_current c.

Lemma is_production_ready_implies_valid : forall c,
  is_production_ready c = true -> ClinicalState.valid c.
Proof.
  intros c H. unfold is_production_ready in H.
  apply andb_true_iff in H. destruct H as [Hv _].
  apply ClinicalState.is_valid_iff. exact Hv.
Qed.

Lemma is_production_ready_implies_current : forall c,
  is_production_ready c = true -> ClinicalState.signs_current c = true.
Proof.
  intros c H. unfold is_production_ready in H.
  apply andb_true_iff in H. destruct H as [_ Hf]. exact Hf.
Qed.

(* Primary classifier: gates on validity AND freshness.
   Returns None if input is out of domain or signs are stale. *)
Definition classify (c : ClinicalState.t) : option Stage.t :=
  if is_production_ready c
  then Some (Classification.classify c)
  else None.

(* Validity-only entry; bypasses staleness check. Retrospective use only. *)
Definition classify_validated_only (c : ClinicalState.t) : option Stage.t :=
  Classification.classify_validated c.

(* Strict-Bell classifier: gates on production-readiness, Bell-strict IIA/IIB. *)
Definition classify_strict (c : ClinicalState.t) : option Stage.t :=
  if is_production_ready c
  then Some (Classification.classify_strict_bell c)
  else None.

(* Diagnosis: gates on production-readiness, runs classifier + differential. *)
Definition diagnose (c : ClinicalState.t) : option Diagnosis.t :=
  if is_production_ready c
  then Some (Classification.diagnose c)
  else None.

(* Organ-failure-aware classifier: single-pass entry that incorporates
   organ assessment into the result. Audit trails record only the final
   stage, eliminating the pre/post-modifier ambiguity of separate calls. *)
Definition classify_with_oa
    (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment)
    : option Stage.t :=
  if is_production_ready c
  then Some (OrganFailureFeedback.classify_with_oa c oa)
  else None.

(* Consensus classifier: returns Some only when procedural and declarative
   agree. Surfaces the principled IIA divergence (PVG without pneumatosis)
   as None rather than picking a reading silently. *)
Definition classify_consensus (c : ClinicalState.t) : option Stage.t :=
  if is_production_ready c
  then BellCriteria.classify_consensus c
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

(* Audit entry creation gated on production-readiness. *)
Definition audit (ts : nat) (c : ClinicalState.t)
    : option (nat * nat * bool) :=
  match classify c with
  | Some s => Some (ts, Stage.to_nat s,
                    Treatment.requires_surgery (Treatment.of_stage s))
  | None => None
  end.

(* Organ-failure-aware audit. Records the final OA-incorporated stage
   in a single audit row, replacing the pre-/post-modifier two-row
   pattern that the post-hoc OrganFailureFeedback.stage_with_organ_failure
   would have produced when paired with the plain audit/. *)
Definition audit_with_oa (ts : nat) (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment)
    : option (nat * nat * bool) :=
  match classify_with_oa c oa with
  | Some s => Some (ts, Stage.to_nat s,
                    Treatment.requires_surgery (Treatment.of_stage s))
  | None => None
  end.

(* --- API guarantees --- *)

Lemma api_classify_sound : forall c s,
  classify c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

(* Stronger soundness: classify also requires fresh signs. *)
Lemma api_classify_requires_current : forall c s,
  classify c = Some s -> ClinicalState.signs_current c = true.
Proof.
  intros c s H. unfold classify in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_current. exact E.
Qed.

Lemma api_classify_agrees : forall c,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  classify c = Some (Classification.classify c).
Proof.
  intros c Hv Hf. unfold classify, is_production_ready.
  apply ClinicalState.is_valid_iff in Hv. rewrite Hv, Hf. reflexivity.
Qed.

Lemma api_strict_sound : forall c s,
  classify_strict c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify_strict in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

Lemma api_strict_requires_current : forall c s,
  classify_strict c = Some s -> ClinicalState.signs_current c = true.
Proof.
  intros c s H. unfold classify_strict in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_current. exact E.
Qed.

Lemma api_diagnose_sound : forall c d,
  diagnose c = Some d -> ClinicalState.valid c.
Proof.
  intros c d H. unfold diagnose in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

Lemma api_diagnose_requires_current : forall c d,
  diagnose c = Some d -> ClinicalState.signs_current c = true.
Proof.
  intros c d H. unfold diagnose in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_current. exact E.
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
  ClinicalState.signs_current c = true ->
  (requires_surgery c = Some true <->
   RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true).
Proof.
  intros c Hv Hf. split.
  - intro H. unfold requires_surgery in H.
    rewrite (api_classify_agrees c Hv Hf) in H.
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
    rewrite (api_classify_agrees c Hv Hf).
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

(* --- Organ-failure-aware API guarantees --- *)

Lemma api_classify_with_oa_sound : forall c oa s,
  classify_with_oa c oa = Some s -> ClinicalState.valid c.
Proof.
  intros c oa s H. unfold classify_with_oa in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

Lemma api_classify_with_oa_requires_current : forall c oa s,
  classify_with_oa c oa = Some s -> ClinicalState.signs_current c = true.
Proof.
  intros c oa s H. unfold classify_with_oa in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_current. exact E.
Qed.

Lemma api_classify_with_oa_agrees : forall c oa,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  classify_with_oa c oa = Some (OrganFailureFeedback.classify_with_oa c oa).
Proof.
  intros c oa Hv Hf. unfold classify_with_oa, is_production_ready.
  apply ClinicalState.is_valid_iff in Hv. rewrite Hv, Hf. reflexivity.
Qed.

(* OA-aware classifier dominates the plain classifier on the same input. *)
Lemma api_classify_with_oa_dominates : forall c oa s_oa s,
  classify_with_oa c oa = Some s_oa ->
  classify c = Some s ->
  Stage.to_nat s <= Stage.to_nat s_oa.
Proof.
  intros c oa s_oa s H1 H2.
  unfold classify_with_oa in H1; unfold classify in H2.
  destruct (is_production_ready c); [|discriminate].
  injection H1 as Hsoa. injection H2 as Hs. subst.
  apply OrganFailureFeedback.classify_with_oa_dominates_classify.
Qed.

(* Surgical boundary preserved through the OA-aware path. *)
Lemma api_classify_with_oa_iff_IIIB : forall c oa,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_with_oa c oa = Some Stage.IIIB.
Proof.
  intros c oa Hv Hf Hperf.
  rewrite (api_classify_with_oa_agrees c oa Hv Hf).
  rewrite (OrganFailureFeedback.classify_with_oa_preserves_IIIB c oa Hperf).
  reflexivity.
Qed.

Lemma api_audit_with_oa_sound : forall ts c oa e,
  audit_with_oa ts c oa = Some e -> ClinicalState.valid c.
Proof.
  intros ts c oa e H. unfold audit_with_oa in H.
  destruct (classify_with_oa c oa) as [s|] eqn:Hc; [|discriminate].
  apply api_classify_with_oa_sound with (oa := oa) (s := s). exact Hc.
Qed.

(* --- Consensus API guarantees --- *)

Lemma api_classify_consensus_sound : forall c s,
  classify_consensus c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify_consensus in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

Lemma api_classify_consensus_requires_current : forall c s,
  classify_consensus c = Some s -> ClinicalState.signs_current c = true.
Proof.
  intros c s H. unfold classify_consensus in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_current. exact E.
Qed.

(* When the API returns Some s through consensus, both internal classifiers
   agreed on s. Stronger than classify alone — caller knows there is no
   procedural-vs-declarative ambiguity for this patient. *)
Lemma api_classify_consensus_both_agree : forall c s,
  classify_consensus c = Some s ->
  Classification.classify c = s /\ BellCriteria.classify_declarative c = s.
Proof.
  intros c s H. unfold classify_consensus in H.
  destruct (is_production_ready c); [|discriminate].
  apply BellCriteria.consensus_some_iff. exact H.
Qed.

(* If the API returns None for an otherwise production-ready input,
   the two classifiers disagreed. This is the deployment signal:
   surface the case for clinician review rather than silent dispatch. *)
Lemma api_classify_consensus_none_means_disagree : forall c,
  is_production_ready c = true ->
  classify_consensus c = None ->
  Classification.classify c <> BellCriteria.classify_declarative c.
Proof.
  intros c Hready H. unfold classify_consensus in H.
  rewrite Hready in H.
  apply BellCriteria.consensus_none_iff_disagree. exact H.
Qed.

(* Surgical-boundary preservation through the consensus path. *)
Lemma api_classify_consensus_iff_IIIB : forall c,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_consensus c = Some Stage.IIIB.
Proof.
  intros c Hv Hf Hperf. unfold classify_consensus, is_production_ready.
  apply ClinicalState.is_valid_iff in Hv. rewrite Hv, Hf. simpl.
  apply BellCriteria.consensus_preserves_IIIB. exact Hperf.
Qed.

End API.
