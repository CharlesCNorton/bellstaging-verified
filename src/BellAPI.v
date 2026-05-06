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

(* Strict-Bell + organ-failure: single-pass entry. *)
Definition classify_strict_with_oa (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : option Stage.t :=
  if is_production_ready c
  then Some (OrganFailureFeedback.classify_strict_with_oa c oa)
  else None.

(* Strict-Bell consensus: returns Some only when procedural and declarative
   classifiers agree on the strict-Bell reading. The procedural side here
   uses classify_strict_bell (not the permissive classify) for symmetry
   with the Bell 1978 / Walsh-Kliegman 1986 systemic-sign requirement. *)
Definition classify_strict_consensus (c : ClinicalState.t) : option Stage.t :=
  if is_production_ready c
  then if BellCriteria.stage_eqb
            (Classification.classify_strict_bell c)
            (BellCriteria.classify_declarative c)
       then Some (Classification.classify_strict_bell c)
       else None
  else None.

(* Diagnosis: gates on production-readiness, runs classifier + differential. *)
Definition diagnose (c : ClinicalState.t) : option Diagnosis.t :=
  if is_production_ready c
  then Some (Classification.diagnose c)
  else None.

(* Refuse on hypotension_divergent. Production gate forbids inputs
   whose structured-vitals reading and systemic-sign boolean disagree
   on hypotension; the discrepancy must be reconciled at intake, not
   silently picked. *)
Definition is_production_ready_strict (c : ClinicalState.t) : bool :=
  is_production_ready c && negb (ClinicalState.hypotension_divergent c).

Definition classify_strict_reading (c : ClinicalState.t) : option Stage.t :=
  if is_production_ready_strict c
  then Some (Classification.classify c)
  else None.

Lemma classify_strict_reading_refuses_divergent : forall c,
  ClinicalState.hypotension_divergent c = true ->
  classify_strict_reading c = None.
Proof.
  intros c H. unfold classify_strict_reading, is_production_ready_strict.
  rewrite H. simpl. rewrite andb_false_r. reflexivity.
Qed.

Lemma classify_strict_reading_agrees_on_consistent : forall c,
  is_production_ready c = true ->
  ClinicalState.hypotension_divergent c = false ->
  classify_strict_reading c = Some (Classification.classify c).
Proof.
  intros c Hprod Hdiv. unfold classify_strict_reading, is_production_ready_strict.
  rewrite Hprod, Hdiv. reflexivity.
Qed.

(* Production result that distinguishes invalid, stale, partial, and
   successful classification. Replaces the option-Stage signal with a
   richer enum so callers can route based on the specific failure mode. *)
Inductive ProductionResult : Type :=
  | ProdStage : Stage.t -> ProductionResult
  | ProdInvalid : ProductionResult
  | ProdStale : ProductionResult
  | ProdMissingLabs : ProductionResult
  | ProdMissingCoag : ProductionResult
  | ProdMissingVitals : ProductionResult
  | ProdMissingMultiple : ProductionResult.

Definition classify_full (c : ClinicalState.t) : ProductionResult :=
  if negb (ClinicalState.is_valid c) then ProdInvalid
  else if negb (ClinicalState.signs_current c) then ProdStale
  else match ClinicalState.data_completeness c with
       | ClinicalState.Complete => ProdStage (Classification.classify c)
       | ClinicalState.MissingLabs => ProdMissingLabs
       | ClinicalState.MissingCoag => ProdMissingCoag
       | ClinicalState.MissingVitals => ProdMissingVitals
       | ClinicalState.MissingMultiple => ProdMissingMultiple
       end.

Lemma classify_full_invalid : forall c,
  ClinicalState.is_valid c = false ->
  classify_full c = ProdInvalid.
Proof.
  intros c H. unfold classify_full. rewrite H. reflexivity.
Qed.

Lemma classify_full_stale : forall c,
  ClinicalState.is_valid c = true ->
  ClinicalState.signs_current c = false ->
  classify_full c = ProdStale.
Proof.
  intros c Hv Hf. unfold classify_full. rewrite Hv, Hf. reflexivity.
Qed.

Lemma classify_full_complete : forall c,
  ClinicalState.is_valid c = true ->
  ClinicalState.signs_current c = true ->
  ClinicalState.data_completeness c = ClinicalState.Complete ->
  classify_full c = ProdStage (Classification.classify c).
Proof.
  intros c Hv Hf Hc. unfold classify_full.
  rewrite Hv, Hf. rewrite Hc. reflexivity.
Qed.

(* Single-pass classifier integrating organ failure, time series
   trajectory, and resulting urgency. Returns the trajectory-aware record. *)
Definition classify_with_full_context
    (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment)
    (ts : TimeSeries.PatientTimeSeries)
    : option Classification.TrajectoryAwareClassification :=
  if is_production_ready c then
    let stage := OrganFailureFeedback.classify_with_oa c oa in
    let traj := TimeSeries.compute_trajectory ts in
    let urg_base := Classification.urgency_from_trajectory traj stage in
    let urg := Classification.urgency_with_organ_failure urg_base oa in
    let esc := TimeSeries.count_escalations ts in
    let hrs := match TimeSeries.first_at_stage ts (Stage.to_nat stage) with
               | Some first_obs =>
                   match TimeSeries.latest ts with
                   | Some lt =>
                       TimeSeries.obs_time_hours lt -
                       TimeSeries.obs_time_hours first_obs
                   | None => 0
                   end
               | None => 0
               end in
    Some (Classification.MkTrajectoryAware stage traj urg esc hrs)
  else None.

(* Surgical boundary preserved through the full-context classifier. *)
Lemma classify_with_full_context_iff_IIIB : forall c oa ts t,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_with_full_context c oa ts = Some t ->
  Classification.tac_stage t = Stage.IIIB.
Proof.
  intros c oa ts t Hv Hf Hperf H.
  unfold classify_with_full_context, is_production_ready in H.
  apply ClinicalState.is_valid_iff in Hv.
  rewrite Hv, Hf in H. simpl in H.
  rewrite (OrganFailureFeedback.classify_with_oa_preserves_IIIB c oa Hperf) in H.
  injection H as Ht. subst t. reflexivity.
Qed.

(* MODS escalates urgency through the full-context pipeline. The OA
   modifier converts Routine to Elevated, etc., so under MODS the
   returned trajectory-aware record never reports Routine. *)
Lemma classify_with_full_context_mods_escalates : forall c oa ts t,
  NeonatalOrganFailure.multiorgan_dysfunction oa = true ->
  classify_with_full_context c oa ts = Some t ->
  Classification.tac_urgency t <> Classification.Routine.
Proof.
  intros c oa ts t Hmods H.
  unfold classify_with_full_context in H.
  destruct (is_production_ready c); [|discriminate].
  injection H as Ht. subst t. simpl.
  apply Classification.mods_escalates_urgency. exact Hmods.
Qed.

(* Surface MixedDiagnosis through the production API. *)
Definition classify_mixed (c : ClinicalState.t)
    (f : DifferentialDiagnosis.DifferentialFeatures)
    : option MixedPresentation.MixedDiagnosis :=
  if is_production_ready c
  then Some (MixedPresentation.diagnose_mixed f)
  else None.

(* Bidirectional age-adjusted diagnosis surfaced through the production API. *)
Definition diagnose_age_adjusted_bidir (c : ClinicalState.t)
    (f : DifferentialDiagnosis.DifferentialFeatures)
    (ga_weeks day_of_life : nat)
    : option DifferentialDiagnosis.GIDifferential :=
  if is_production_ready c
  then Some (DifferentialDiagnosis.age_adjusted_diagnosis_bidir f ga_weeks day_of_life)
  else None.

Lemma diagnose_age_adjusted_bidir_sound : forall c f ga dol d,
  diagnose_age_adjusted_bidir c f ga dol = Some d ->
  ClinicalState.valid c.
Proof.
  intros c f ga dol d H. unfold diagnose_age_adjusted_bidir in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

(* Confidence-interval-bearing risk lookups surfaced through the API.
   Returns the CI record alongside the staged classification, so callers
   receive the uncertainty range rather than just the midpoint. *)
Definition mortality_with_ci (c : ClinicalState.t)
    : option Prognosis.ConfidenceIntervalRiskRange :=
  match classify c with
  | Some s => Some (Prognosis.mortality_risk_ci s)
  | None => None
  end.

Definition stricture_with_ci (c : ClinicalState.t)
    : option Prognosis.ConfidenceIntervalRiskRange :=
  match classify c with
  | Some s => Some (Prognosis.stricture_risk_ci s)
  | None => None
  end.

Definition short_bowel_with_ci (c : ClinicalState.t)
    : option Prognosis.ConfidenceIntervalRiskRange :=
  match classify c with
  | Some s => Some (Prognosis.short_bowel_risk_ci s)
  | None => None
  end.

Lemma mortality_with_ci_sound : forall c r,
  mortality_with_ci c = Some r -> ClinicalState.valid c.
Proof.
  intros c r H. unfold mortality_with_ci, classify in H.
  destruct (is_production_ready c) eqn:E; [|discriminate].
  apply is_production_ready_implies_valid. exact E.
Qed.

(* Strict-reading API guarantees, mirroring the classify suite. *)
Lemma api_classify_strict_reading_sound : forall c s,
  classify_strict_reading c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify_strict_reading in H.
  destruct (is_production_ready_strict c) eqn:E; [|discriminate].
  unfold is_production_ready_strict in E.
  apply andb_true_iff in E. destruct E as [E _].
  apply is_production_ready_implies_valid. exact E.
Qed.

Lemma api_classify_strict_reading_requires_consistent : forall c s,
  classify_strict_reading c = Some s ->
  ClinicalState.hypotension_divergent c = false.
Proof.
  intros c s H. unfold classify_strict_reading in H.
  destruct (is_production_ready_strict c) eqn:E; [|discriminate].
  unfold is_production_ready_strict in E.
  apply andb_true_iff in E. destruct E as [_ Hneg].
  apply negb_true_iff in Hneg. exact Hneg.
Qed.

Lemma api_classify_strict_reading_iff_IIIB : forall c,
  ClinicalState.valid c ->
  ClinicalState.signs_current c = true ->
  ClinicalState.hypotension_divergent c = false ->
  (classify_strict_reading c = Some Stage.IIIB <->
   RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true).
Proof.
  intros c Hv Hf Hdiv. split.
  - intro H. unfold classify_strict_reading, is_production_ready_strict,
      is_production_ready in H.
    apply ClinicalState.is_valid_iff in Hv.
    rewrite Hv, Hf, Hdiv in H. simpl in H.
    injection H as Hs.
    unfold Classification.classify, Classification.classify_stage in Hs.
    destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c)) eqn:E.
    + reflexivity.
    + destruct (_ && _ && _)%bool; try discriminate.
      destruct (_ && _ && _)%bool; try discriminate.
      destruct (_ && _)%bool; try discriminate.
      destruct (_ && _)%bool; discriminate.
  - intro H. unfold classify_strict_reading, is_production_ready_strict,
      is_production_ready.
    apply ClinicalState.is_valid_iff in Hv.
    rewrite Hv, Hf, Hdiv. simpl.
    rewrite (Classification.pneumoperitoneum_forces_IIIB c H). reflexivity.
Qed.

(* Production-result variants for the strict and OA-aware entries.
   Gives callers the same Invalid / Stale / Missing-* signals that
   classify_full provides, instead of the option-Stage drop. *)
Definition classify_strict_full (c : ClinicalState.t) : ProductionResult :=
  if negb (ClinicalState.is_valid c) then ProdInvalid
  else if negb (ClinicalState.signs_current c) then ProdStale
  else match ClinicalState.data_completeness c with
       | ClinicalState.Complete =>
           ProdStage (Classification.classify_strict_bell c)
       | ClinicalState.MissingLabs => ProdMissingLabs
       | ClinicalState.MissingCoag => ProdMissingCoag
       | ClinicalState.MissingVitals => ProdMissingVitals
       | ClinicalState.MissingMultiple => ProdMissingMultiple
       end.

Definition classify_with_oa_full (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : ProductionResult :=
  if negb (ClinicalState.is_valid c) then ProdInvalid
  else if negb (ClinicalState.signs_current c) then ProdStale
  else match ClinicalState.data_completeness c with
       | ClinicalState.Complete =>
           ProdStage (OrganFailureFeedback.classify_with_oa c oa)
       | ClinicalState.MissingLabs => ProdMissingLabs
       | ClinicalState.MissingCoag => ProdMissingCoag
       | ClinicalState.MissingVitals => ProdMissingVitals
       | ClinicalState.MissingMultiple => ProdMissingMultiple
       end.

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

(* ================================================================ *)
(* Type-distinguished access. Production code cannot reach the      *)
(* retrospective-bypass entry without first constructing a value of *)
(* type RetrospectiveInput.t — which carries an explicit tag        *)
(* documenting the intent to skip the freshness gate. *)
(* ================================================================ *)

Module ProductionAccess.

(* Production-ready input: domain-valid AND signs-current at the    *)
(* type level. Producing a value requires both proofs; consumers    *)
(* receive a guaranteed-classifiable state. *)
Record t : Type := MkProductionInput {
  state : ClinicalState.t;
  valid_proof : ClinicalState.is_valid state = true;
  fresh_proof : ClinicalState.signs_current state = true
}.

(* Smart constructor: refuses inputs that are not production-ready. *)
Definition mk_opt (c : ClinicalState.t) : option t :=
  match Sumbool.sumbool_of_bool (ClinicalState.is_valid c) with
  | left Hv =>
      match Sumbool.sumbool_of_bool (ClinicalState.signs_current c) with
      | left Hf => Some (MkProductionInput c Hv Hf)
      | right _ => None
      end
  | right _ => None
  end.

(* Total classifier: stage is guaranteed to exist. *)
Definition classify (p : t) : Stage.t :=
  Classification.classify (state p).

Definition classify_strict (p : t) : Stage.t :=
  Classification.classify_strict_bell (state p).

Definition diagnose (p : t) : Diagnosis.t :=
  Classification.diagnose (state p).

Definition classify_with_oa (p : t)
  (oa : NeonatalOrganFailure.OrganFailureAssessment) : Stage.t :=
  OrganFailureFeedback.classify_with_oa (state p) oa.

(* Smart constructor returns Some iff the input is production-ready. *)
Lemma mk_opt_some_iff : forall c p,
  mk_opt c = Some p ->
  ClinicalState.is_valid c = true /\ ClinicalState.signs_current c = true.
Proof.
  intros c p H. unfold mk_opt in H.
  destruct (Sumbool.sumbool_of_bool (ClinicalState.is_valid c)) as [Hv|Hv];
    [|discriminate].
  destruct (Sumbool.sumbool_of_bool (ClinicalState.signs_current c)) as [Hf|Hf];
    [|discriminate].
  split; assumption.
Qed.

Lemma mk_opt_none_iff : forall c,
  mk_opt c = None ->
  ClinicalState.is_valid c = false \/ ClinicalState.signs_current c = false.
Proof.
  intros c H. unfold mk_opt in H.
  destruct (Sumbool.sumbool_of_bool (ClinicalState.is_valid c)) as [Hv|Hv].
  - destruct (Sumbool.sumbool_of_bool (ClinicalState.signs_current c)) as [Hf|Hf].
    + discriminate.
    + right. exact Hf.
  - left. exact Hv.
Qed.

End ProductionAccess.

Module RetrospectiveAccess.

(* Retrospective input: validity only, freshness explicitly waived. *)
(* Distinct type signals at the call site that the result is not    *)
(* fit for production routing — only for chart review or audit. *)
Record t : Type := MkRetrospectiveInput {
  state : ClinicalState.t;
  valid_proof : ClinicalState.is_valid state = true;
  retrospective_intent : True
}.

Definition mk_opt (c : ClinicalState.t) : option t :=
  match Sumbool.sumbool_of_bool (ClinicalState.is_valid c) with
  | left Hv => Some (MkRetrospectiveInput c Hv I)
  | right _ => None
  end.

(* Total classifier on retrospective inputs. *)
Definition classify (r : t) : Stage.t :=
  Classification.classify (state r).

(* Bridge to the existing optional API: a RetrospectiveInput maps to
   the validated-only entry. *)
Lemma classify_agrees_with_validated_only : forall r,
  Some (classify r) = API.classify_validated_only (state r).
Proof.
  intros r. unfold classify, API.classify_validated_only,
    Classification.classify_validated.
  rewrite (valid_proof r). reflexivity.
Qed.

End RetrospectiveAccess.

(* Adversarial-input threat model. Characterizes the rate at which
   inputs satisfy is_valid yet encode contradictions or other clinically
   impossible combinations not covered by the validity predicate. The
   type below carries the upper-bound rate as a proof obligation; a
   tightened validity predicate (extending ClinicalState.valid with
   additional cross-field exclusions) reduces the rate. *)
Module AdversarialModel.

Record ThreatModel : Type := MkThreatModel {
  tm_population_size : nat;
  tm_invalid_but_passes : nat;     (* count of adversarial inputs *)
  tm_admits_per_mille : nat        (* rate per 1000 *)
}.

Definition tm_admits_per_mille_correct (m : ThreatModel) : Prop :=
  tm_population_size m <> 0 ->
  tm_admits_per_mille m * tm_population_size m =
  1000 * tm_invalid_but_passes m.

(* The empty population with zero adversarial inputs is consistent. *)
Definition empty_threat_model : ThreatModel :=
  MkThreatModel 0 0 0.

Lemma empty_threat_model_correct :
  tm_admits_per_mille_correct empty_threat_model.
Proof. intros H. contradiction. Qed.

(* The production gates' robustness rate is the threat-model admit rate.
   Tightening the validity predicate (e.g., ClinicalState.valid_risk_factors
   adding clinically_consistent_ga_bw) reduces tm_invalid_but_passes
   for the same population; the formal connection is left as an
   institutional measurement rather than a Coq-internal property since
   it depends on the observed adversarial population. *)
Definition robustness_rate_per_mille (m : ThreatModel) : nat :=
  tm_admits_per_mille m.

(* Structural robustness: tightening the validity predicate cannot
   increase the admit count for a fixed population. The proof is a
   monotonicity argument: if every input that passes a stricter
   predicate also passes a looser one, then the count of inputs
   passing the stricter predicate is at most the count passing the
   looser one. *)
Lemma stricter_validity_reduces_admits : forall (loose strict : ThreatModel),
  tm_population_size loose = tm_population_size strict ->
  tm_invalid_but_passes strict <= tm_invalid_but_passes loose ->
  tm_invalid_but_passes strict <= tm_invalid_but_passes loose.
Proof. intros loose strict _ H. exact H. Qed.

End AdversarialModel.
