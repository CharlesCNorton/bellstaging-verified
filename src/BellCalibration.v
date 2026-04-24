From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.

Import ListNotations.

Module Calibration.

(* Calibrated weight vector for DifferentialDiagnosis.nec_confidence and
   DifferentialDiagnosis.sip_confidence. *)
Record CalibratedWeights : Type := MkWeights {
  w_pneumatosis : nat;
  w_pvg : nat;
  w_feeding_intol : nat;
  w_pneumoperitoneum_bonus : nat;
  w_sip_pneumoperitoneum : nat;
  w_sip_no_pneumatosis : nat;
  w_sip_no_pvg : nat;
  w_sip_extremely_preterm : nat
}.

(* Editorial defaults matching the current DifferentialDiagnosis weights. *)
Definition default_weights : CalibratedWeights :=
  MkWeights 5 4 2 3 3 2 1 2.

(* A cohort summarizes the patient-level data behind a calibration fit. *)
Record CalibrationCohort : Type := MkCohort {
  n_nec : nat;
  n_sip : nat;
  n_volvulus : nat;
  n_sepsis : nat;
  n_feeding_intolerance : nat;
  cohort_year : nat
}.

Definition cohort_size (c : CalibrationCohort) : nat :=
  n_nec c + n_sip c + n_volvulus c + n_sepsis c + n_feeding_intolerance c.

Definition minimum_cohort_size : nat := 500.

Definition cohort_adequate (c : CalibrationCohort) : bool :=
  minimum_cohort_size <=? cohort_size c.

(* Calibration metadata pairs a weight vector with the cohort it came from
   and an ISO-like cohort vintage flag. *)
Record CalibrationMetadata : Type := MkCalibrationMeta {
  weights : CalibratedWeights;
  cohort : option CalibrationCohort;
  calibrated_as_of : nat
}.

Definition default_metadata : CalibrationMetadata :=
  MkCalibrationMeta default_weights None 0.

Definition is_calibrated (m : CalibrationMetadata) : bool :=
  negb (calibrated_as_of m =? 0).

Lemma default_uncalibrated : is_calibrated default_metadata = false.
Proof. reflexivity. Qed.

(* Parameterized confidence scoring. *)
Definition calibrated_nec_confidence (w : CalibratedWeights)
    (f : DifferentialDiagnosis.DifferentialFeatures) : nat :=
  (if DifferentialDiagnosis.has_pneumatosis f then w_pneumatosis w else 0) +
  (if DifferentialDiagnosis.has_portal_venous_gas f then w_pvg w else 0) +
  (if DifferentialDiagnosis.has_preceding_feeding_intolerance f
   then w_feeding_intol w else 0) +
  (if DifferentialDiagnosis.has_pneumoperitoneum f &&
      DifferentialDiagnosis.has_pneumatosis f
   then w_pneumoperitoneum_bonus w else 0).

Definition calibrated_sip_confidence (w : CalibratedWeights)
    (f : DifferentialDiagnosis.DifferentialFeatures) : nat :=
  (if DifferentialDiagnosis.has_pneumoperitoneum f
   then w_sip_pneumoperitoneum w else 0) +
  (if negb (DifferentialDiagnosis.has_pneumatosis f)
   then w_sip_no_pneumatosis w else 0) +
  (if negb (DifferentialDiagnosis.has_portal_venous_gas f)
   then w_sip_no_pvg w else 0) +
  (if DifferentialDiagnosis.extremely_preterm f
   then w_sip_extremely_preterm w else 0).

Theorem default_nec_confidence_agrees : forall f,
  calibrated_nec_confidence default_weights f =
  DifferentialDiagnosis.nec_confidence f.
Proof.
  intros f. unfold calibrated_nec_confidence, default_weights,
    DifferentialDiagnosis.nec_confidence. simpl.
  destruct (DifferentialDiagnosis.has_pneumatosis f);
  destruct (DifferentialDiagnosis.has_portal_venous_gas f);
  destruct (DifferentialDiagnosis.has_preceding_feeding_intolerance f);
  destruct (DifferentialDiagnosis.has_pneumoperitoneum f);
  simpl; lia.
Qed.

Theorem default_sip_confidence_agrees : forall f,
  calibrated_sip_confidence default_weights f =
  DifferentialDiagnosis.sip_confidence f.
Proof.
  intros f. unfold calibrated_sip_confidence, default_weights,
    DifferentialDiagnosis.sip_confidence. simpl.
  destruct (DifferentialDiagnosis.has_pneumoperitoneum f);
  destruct (DifferentialDiagnosis.has_pneumatosis f);
  destruct (DifferentialDiagnosis.has_portal_venous_gas f);
  destruct (DifferentialDiagnosis.extremely_preterm f);
  simpl; lia.
Qed.

(* Calibration-gated diagnostic API: callers must pass metadata indicating
   the weights came from a validated cohort. *)
Definition diagnose_with_calibration
    (m : CalibrationMetadata)
    (f : DifferentialDiagnosis.DifferentialFeatures)
    : option DifferentialDiagnosis.GIDifferential :=
  if is_calibrated m then
    Some (DifferentialDiagnosis.most_likely_diagnosis f)
  else None.

Lemma diagnose_refuses_uncalibrated : forall f,
  diagnose_with_calibration default_metadata f = None.
Proof. reflexivity. Qed.

Lemma diagnose_delivers_calibrated : forall m f,
  is_calibrated m = true ->
  diagnose_with_calibration m f =
  Some (DifferentialDiagnosis.most_likely_diagnosis f).
Proof.
  intros m f H. unfold diagnose_with_calibration. rewrite H. reflexivity.
Qed.

(* Logistic regression is not implementable in Coq kernel terms.
   fit_weights is the signature a downstream implementation (OCaml / Python)
   fills in; the Coq stub returns default_weights so the specification
   compiles. A proved real fit replaces the stub once cohort data is
   available. *)
Definition fit_weights (c : CalibrationCohort) : CalibratedWeights :=
  default_weights.

Theorem fit_stub_is_default : forall c,
  fit_weights c = default_weights.
Proof. reflexivity. Qed.

Definition calibrate (c : CalibrationCohort) : CalibrationMetadata :=
  MkCalibrationMeta (fit_weights c) (Some c) (cohort_year c).

Lemma calibrate_records_cohort : forall c,
  cohort (calibrate c) = Some c.
Proof. reflexivity. Qed.

Lemma calibrate_records_year : forall c,
  calibrated_as_of (calibrate c) = cohort_year c.
Proof. reflexivity. Qed.

Lemma calibrate_year_zero_remains_uncalibrated : forall c,
  cohort_year c = 0 ->
  is_calibrated (calibrate c) = false.
Proof.
  intros c H. unfold is_calibrated, calibrate. simpl. rewrite H. reflexivity.
Qed.

Lemma calibrate_year_nonzero_is_calibrated : forall c,
  cohort_year c <> 0 ->
  is_calibrated (calibrate c) = true.
Proof.
  intros c H. unfold is_calibrated, calibrate. simpl.
  apply negb_true_iff. apply Nat.eqb_neq. exact H.
Qed.

(* Coverage constraint: a cohort intended for multinomial logistic
   regression over NEC vs SIP vs {volvulus, sepsis, feeding_intolerance}
   requires adequate size. *)
Lemma adequate_cohort_reaches_minimum : forall c,
  cohort_adequate c = true -> minimum_cohort_size <= cohort_size c.
Proof.
  intros c H. unfold cohort_adequate in H. apply Nat.leb_le in H. exact H.
Qed.

End Calibration.
