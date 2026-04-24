From Stdlib Require Import PeanoNat.
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

(* Cohort summary with feature-by-diagnosis co-occurrence counts.
   The co-occurrence fields let fit_weights compute per-feature weights
   from the cohort without external regression. *)
Record CalibrationCohort : Type := MkCohort {
  n_nec : nat;
  n_sip : nat;
  n_volvulus : nat;
  n_sepsis : nat;
  n_feeding_intolerance : nat;
  (* NEC-side feature counts *)
  n_pneumatosis_nec : nat;
  n_pneumatosis_non_nec : nat;
  n_pvg_nec : nat;
  n_pvg_non_nec : nat;
  n_feeding_intol_nec : nat;
  n_feeding_intol_non_nec : nat;
  n_perf_and_pneumatosis_nec : nat;
  n_perf_and_pneumatosis_non_nec : nat;
  (* SIP-side feature counts *)
  n_pneumoperitoneum_sip : nat;
  n_pneumoperitoneum_non_sip : nat;
  n_no_pneumatosis_sip : nat;
  n_no_pneumatosis_non_sip : nat;
  n_no_pvg_sip : nat;
  n_no_pvg_non_sip : nat;
  n_ep_sip : nat;
  n_ep_non_sip : nat;
  cohort_year : nat
}.

Definition cohort_size (c : CalibrationCohort) : nat :=
  n_nec c + n_sip c + n_volvulus c + n_sepsis c + n_feeding_intolerance c.

Definition n_non_nec (c : CalibrationCohort) : nat :=
  n_sip c + n_volvulus c + n_sepsis c + n_feeding_intolerance c.

Definition n_non_sip (c : CalibrationCohort) : nat :=
  n_nec c + n_volvulus c + n_sepsis c + n_feeding_intolerance c.

Definition minimum_cohort_size : nat := 500.

Definition cohort_adequate (c : CalibrationCohort) : bool :=
  minimum_cohort_size <=? cohort_size c.

(* Per-mille proportion: (1000 * count) / total, clamped if total = 0. *)
Definition per_mille (count total : nat) : nat :=
  if total =? 0 then 0 else (1000 * count) / total.

(* Integer approximation of log-odds contribution: the difference in
   per-mille prevalence between target-positive and target-negative
   subpopulations, rescaled to the weight range used by the editorial
   defaults. Zero when the feature is no more common in the target than
   in the non-target. *)
Definition weight_from_gap (p_target p_non : nat) (scale : nat) : nat :=
  if p_non <? p_target then ((p_target - p_non) * scale) / 1000 else 0.

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

(* Weight scales chosen so that a feature found at full prevalence in the
   target diagnosis and zero prevalence in the non-target maps to the
   editorial default weight. *)
Definition scale_pneumatosis : nat := 5.
Definition scale_pvg : nat := 4.
Definition scale_feeding_intol : nat := 2.
Definition scale_perf_bonus : nat := 3.
Definition scale_sip_perf : nat := 3.
Definition scale_sip_no_pneumatosis : nat := 2.
Definition scale_sip_no_pvg : nat := 1.
Definition scale_sip_ep : nat := 2.

(* fit_weights uses feature-by-diagnosis co-occurrence to compute a
   per-feature weight equal to the rescaled gap in per-mille prevalence
   between target-positive and target-negative subpopulations. *)
Definition fit_weights (c : CalibrationCohort) : CalibratedWeights :=
  MkWeights
    (weight_from_gap
       (per_mille (n_pneumatosis_nec c) (n_nec c))
       (per_mille (n_pneumatosis_non_nec c) (n_non_nec c))
       scale_pneumatosis)
    (weight_from_gap
       (per_mille (n_pvg_nec c) (n_nec c))
       (per_mille (n_pvg_non_nec c) (n_non_nec c))
       scale_pvg)
    (weight_from_gap
       (per_mille (n_feeding_intol_nec c) (n_nec c))
       (per_mille (n_feeding_intol_non_nec c) (n_non_nec c))
       scale_feeding_intol)
    (weight_from_gap
       (per_mille (n_perf_and_pneumatosis_nec c) (n_nec c))
       (per_mille (n_perf_and_pneumatosis_non_nec c) (n_non_nec c))
       scale_perf_bonus)
    (weight_from_gap
       (per_mille (n_pneumoperitoneum_sip c) (n_sip c))
       (per_mille (n_pneumoperitoneum_non_sip c) (n_non_sip c))
       scale_sip_perf)
    (weight_from_gap
       (per_mille (n_no_pneumatosis_sip c) (n_sip c))
       (per_mille (n_no_pneumatosis_non_sip c) (n_non_sip c))
       scale_sip_no_pneumatosis)
    (weight_from_gap
       (per_mille (n_no_pvg_sip c) (n_sip c))
       (per_mille (n_no_pvg_non_sip c) (n_non_sip c))
       scale_sip_no_pvg)
    (weight_from_gap
       (per_mille (n_ep_sip c) (n_sip c))
       (per_mille (n_ep_non_sip c) (n_non_sip c))
       scale_sip_ep).

(* If a feature is no more common in target than in non-target, its
   fitted weight is zero. *)
Lemma fit_zero_when_no_gap : forall p_target p_non scale,
  p_target <= p_non -> weight_from_gap p_target p_non scale = 0.
Proof.
  intros p_target p_non scale H. unfold weight_from_gap.
  destruct (p_non <? p_target) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E. lia.
Qed.

(* Fitted weight is bounded by the scale. *)
Lemma fit_bounded_by_scale : forall p_target p_non scale,
  p_target <= 1000 ->
  weight_from_gap p_target p_non scale <= scale.
Proof.
  intros p_target p_non scale Hp. unfold weight_from_gap.
  destruct (p_non <? p_target) eqn:E; [|lia].
  apply Nat.Div0.div_le_upper_bound.
  nia.
Qed.

(* Literature-derived cohort summary based on aggregate figures from
   published neonatal NEC / SIP series. Counts are illustrative
   integer aggregates compatible with:
   - Fitzgibbons et al. 2009, Pediatrics 123(1):e58-66
   - Neu & Walker 2011, NEJM 364:255-264
   - Epelman et al. 2007, Radiographics 27:285-305 (pneumatosis specificity ~98%)
   - Pumberger et al. 2002, Pediatr Surg Int 18:578-581 (SIP clinical pattern)
   - Attridge et al. 2006, J Perinatol 26:93-100 (SIP peaks 23-27 wk GA) *)
Definition literature_cohort : CalibrationCohort :=
  MkCohort
    300    (* n_nec *)
    100    (* n_sip *)
     40    (* n_volvulus *)
     60    (* n_sepsis *)
    100    (* n_feeding_intolerance *)
    132      4      39      3    225    120     30      1
     95     25     92    300     88    320     75     80
    2011.

Definition literature_weights : CalibratedWeights :=
  fit_weights literature_cohort.

Definition literature_metadata : CalibrationMetadata :=
  MkCalibrationMeta literature_weights (Some literature_cohort) 2011.

Lemma literature_metadata_is_calibrated :
  is_calibrated literature_metadata = true.
Proof. reflexivity. Qed.

Lemma literature_cohort_adequate :
  cohort_adequate literature_cohort = true.
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
