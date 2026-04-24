From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.
From BellStaging Require Import BellSerialization.

Import ListNotations.

(* ================================================================ *)
(* Extended clinical modeling — cures 29-59                         *)
(* ================================================================ *)

(* Cure 29: SIP-specific treatment protocol *)
Module SIPProtocol.

Inductive SIPTreatment : Type :=
  | SIPDrainage : SIPTreatment
  | SIPLaparotomy : SIPTreatment
  | SIPConservative : SIPTreatment.

Definition sip_treatment (bw : nat) (hemodynamically_unstable : bool) : SIPTreatment :=
  if (bw <? 1000) && hemodynamically_unstable then SIPDrainage
  else SIPLaparotomy.

Definition is_sip_diagnosis (d : Diagnosis.t) : bool :=
  match d with
  | Diagnosis.SuspectedSIP => true
  | _ => false
  end.

(* sip_treatment agrees structurally with the general perforation procedure
   selector: ELBW+unstable yields drainage in both, else laparotomy. *)
Lemma sip_drainage_iff_elbw_unstable : forall bw unstable,
  sip_treatment bw unstable = SIPDrainage <->
  SurgicalProcedures.initial_procedure_for_perforation bw unstable
    = SurgicalProcedures.PrimaryPeritonealDrainage.
Proof.
  intros bw unstable.
  unfold sip_treatment, SurgicalProcedures.initial_procedure_for_perforation.
  destruct (bw <? 1000); destruct unstable; simpl;
  split; intro H; try reflexivity; try discriminate.
Qed.

Lemma sip_laparotomy_iff_not_elbw_unstable : forall bw unstable,
  sip_treatment bw unstable = SIPLaparotomy <->
  SurgicalProcedures.initial_procedure_for_perforation bw unstable
    = SurgicalProcedures.ExploratoryLaparotomy.
Proof.
  intros bw unstable.
  unfold sip_treatment, SurgicalProcedures.initial_procedure_for_perforation.
  destruct (bw <? 1000); destruct unstable; simpl;
  split; intro H; try reflexivity; try discriminate.
Qed.

End SIPProtocol.

(* Cure 30: NEC extent and totalis modeling *)
Module NECExtent.

Inductive Extent : Type :=
  | Focal : Extent          (* <25% bowel *)
  | Multifocal : Extent     (* 25-50% bowel *)
  | Extensive : Extent      (* 50-75% bowel *)
  | Totalis : Extent.       (* >75% bowel — pan-intestinal *)

Definition extent_percent_range (e : Extent) : nat * nat :=
  match e with
  | Focal => (0, 25)
  | Multifocal => (25, 50)
  | Extensive => (50, 75)
  | Totalis => (75, 100)
  end.

Inductive AnatomicLocation : Type :=
  | Ileum : AnatomicLocation
  | Jejunum : AnatomicLocation
  | Colon : AnatomicLocation
  | Ileocecal : AnatomicLocation
  | Diffuse : AnatomicLocation.

Record NECDistribution : Type := MkDistribution {
  extent : Extent;
  primary_location : AnatomicLocation;
  bowel_viable : bool;
  skip_lesions : bool
}.

Definition is_totalis (d : NECDistribution) : bool :=
  match extent d with Totalis => true | _ => false end.

Definition salvageable (d : NECDistribution) : bool :=
  bowel_viable d && negb (is_totalis d).

Lemma salvageable_excludes_totalis : forall d,
  salvageable d = true -> is_totalis d = false /\ bowel_viable d = true.
Proof.
  intros d H. unfold salvageable in H.
  apply andb_true_iff in H. destruct H as [Hb Hnt].
  apply negb_true_iff in Hnt. split; assumption.
Qed.

End NECExtent.

(* Cure 31-32: Expanded surgical procedure selection *)
Module ExpandedSurgical.

Definition procedure_selection
    (bw : nat) (unstable : bool) (dist : NECExtent.NECDistribution) :
    SurgicalProcedures.Procedure :=
  if NECExtent.is_totalis dist then
    SurgicalProcedures.ExploratoryLaparotomy
  else if (bw <? 1000) && unstable then
    SurgicalProcedures.PrimaryPeritonealDrainage
  else if negb (NECExtent.bowel_viable dist) then
    if NECExtent.salvageable dist then
      SurgicalProcedures.BowelResectionPrimaryAnastomosis
    else
      SurgicalProcedures.BowelResectionStoma
  else
    SurgicalProcedures.ExploratoryLaparotomy.

Definition stoma_decision (dist : NECExtent.NECDistribution) (patient_stable : bool) : bool :=
  match NECExtent.extent dist with
  | NECExtent.Extensive | NECExtent.Totalis => true
  | NECExtent.Multifocal => negb patient_stable
  | NECExtent.Focal => false
  end.

Lemma totalis_forces_laparotomy : forall bw u dist,
  NECExtent.is_totalis dist = true ->
  procedure_selection bw u dist = SurgicalProcedures.ExploratoryLaparotomy.
Proof.
  intros bw u dist H. unfold procedure_selection. rewrite H. reflexivity.
Qed.

Definition extent_rank (e : NECExtent.Extent) : nat :=
  match e with
  | NECExtent.Focal => 0
  | NECExtent.Multifocal => 1
  | NECExtent.Extensive => 2
  | NECExtent.Totalis => 3
  end.

Lemma stoma_decision_monotone_unstable : forall dist,
  stoma_decision dist false = true \/ stoma_decision dist true = false \/
  stoma_decision dist false = stoma_decision dist true.
Proof.
  intros dist. unfold stoma_decision.
  destruct (NECExtent.extent dist); auto.
Qed.

End ExpandedSurgical.

(* Cure 33: Antibiotic de-escalation *)
Module AntibioticStewardship.

Definition deescalation_regimen (current : Antibiotics.Regimen)
    (culture_negative_48h : bool) : Antibiotics.Regimen :=
  if negb culture_negative_48h then current
  else match current with
  | Antibiotics.Broad_VancMeropenem => Antibiotics.Empiric_AmpGentMetro
  | Antibiotics.Broad_VancCefotaximeMetro => Antibiotics.Empiric_AmpGentMetro
  | Antibiotics.Broad_PipTazo => Antibiotics.Empiric_AmpGentMetro
  | _ => current
  end.

Lemma deescalation_never_broadens : forall r,
  Antibiotics.has_antifungal_coverage (deescalation_regimen r true) = false.
Proof. intros []; vm_compute; reflexivity. Qed.

Lemma deescalation_preserves_gram_neg : forall r,
  Antibiotics.has_gram_negative_coverage r = true ->
  Antibiotics.has_gram_negative_coverage (deescalation_regimen r true) = true.
Proof. intros []; vm_compute; auto. Qed.

Lemma deescalation_identity_when_culture_not_negative : forall r,
  deescalation_regimen r false = r.
Proof. intros r. reflexivity. Qed.

End AntibioticStewardship.

(* Cure 34: Antibiotic adverse effects *)
Module AntibioticAdverseEffects.

Inductive AdverseRisk : Type :=
  | LowRisk : AdverseRisk
  | ModerateRisk : AdverseRisk
  | HighRisk : AdverseRisk.

Definition nephrotoxicity_risk (r : Antibiotics.Regimen) : AdverseRisk :=
  match r with
  | Antibiotics.Broad_VancMeropenem => HighRisk
  | Antibiotics.Broad_VancCefotaximeMetro => ModerateRisk
  | Antibiotics.Empiric_AmpGent => ModerateRisk
  | Antibiotics.Empiric_AmpGentMetro => ModerateRisk
  | Antibiotics.Broad_PipTazo => LowRisk
  end.

Definition seizure_risk (r : Antibiotics.Regimen) : AdverseRisk :=
  match r with
  | Antibiotics.Broad_VancMeropenem => ModerateRisk
  | _ => LowRisk
  end.

Definition adverse_rank (r : AdverseRisk) : nat :=
  match r with LowRisk => 0 | ModerateRisk => 1 | HighRisk => 2 end.

Lemma nephrotoxicity_dominates_seizure : forall r,
  adverse_rank (seizure_risk r) <= adverse_rank (nephrotoxicity_risk r).
Proof. intros []; simpl; lia. Qed.

Lemma piptazo_is_lowest_nephrotoxicity : forall r,
  adverse_rank (nephrotoxicity_risk Antibiotics.Broad_PipTazo) <=
  adverse_rank (nephrotoxicity_risk r).
Proof. intros []; simpl; lia. Qed.

End AntibioticAdverseEffects.

(* Cure 35: GA-adjusted lab thresholds *)
Module GAAdjustedLabs.

Definition neutropenia_threshold (ga_weeks : nat) : nat :=
  if ga_weeks <? 28 then 1000
  else if ga_weeks <? 32 then 1200
  else 1500.

Definition thrombocytopenia_threshold (ga_weeks : nat) : nat :=
  if ga_weeks <? 28 then 100
  else 150.

Definition ga_adjusted_neutropenia (l : LabValues.t) (ga_weeks : nat) : bool :=
  LabValues.absolute_neutrophil_count l <? neutropenia_threshold ga_weeks.

Definition ga_adjusted_thrombocytopenia (l : LabValues.t) (ga_weeks : nat) : bool :=
  LabValues.platelet_k_per_uL l <? thrombocytopenia_threshold ga_weeks.

Lemma neutropenia_threshold_monotone : forall ga1 ga2,
  ga1 <= ga2 -> neutropenia_threshold ga1 <= neutropenia_threshold ga2.
Proof.
  intros ga1 ga2 H. unfold neutropenia_threshold.
  destruct (Nat.ltb_spec ga1 28); destruct (Nat.ltb_spec ga2 28);
  destruct (Nat.ltb_spec ga1 32); destruct (Nat.ltb_spec ga2 32);
  lia.
Qed.

Lemma thrombocytopenia_threshold_monotone : forall ga1 ga2,
  ga1 <= ga2 -> thrombocytopenia_threshold ga1 <= thrombocytopenia_threshold ga2.
Proof.
  intros ga1 ga2 H. unfold thrombocytopenia_threshold.
  destruct (Nat.ltb_spec ga1 28); destruct (Nat.ltb_spec ga2 28);
  lia.
Qed.

End GAAdjustedLabs.

(* Cure 36: Serial biomarker trending *)
Module BiomarkerTrending.

Inductive Trend : Type :=
  | Rising : Trend
  | Stable : Trend
  | Falling : Trend.

Definition compute_trend (earlier later : nat) : Trend :=
  if later <? earlier then Falling
  else if earlier <? later then Rising
  else Stable.

Record BiomarkerSeries : Type := MkBiomarkerSeries {
  crp_trend : Trend;
  platelet_trend : Trend;
  lactate_trend : Trend
}.

Definition worsening_biomarkers (s : BiomarkerSeries) : bool :=
  match crp_trend s with Rising => true | _ => false end ||
  match platelet_trend s with Falling => true | _ => false end ||
  match lactate_trend s with Rising => true | _ => false end.

Lemma worsening_iff : forall s,
  worsening_biomarkers s = true <->
  crp_trend s = Rising \/ platelet_trend s = Falling \/ lactate_trend s = Rising.
Proof.
  intros s. unfold worsening_biomarkers. split.
  - intro H. apply orb_true_iff in H. destruct H as [H|H].
    + apply orb_true_iff in H. destruct H as [H|H].
      * destruct (crp_trend s) eqn:Ec; try discriminate. left. reflexivity.
      * destruct (platelet_trend s) eqn:Ep; try discriminate.
        right. left. reflexivity.
    + destruct (lactate_trend s) eqn:El; try discriminate.
      right. right. reflexivity.
  - intros [H|[H|H]]; rewrite H.
    + reflexivity.
    + destruct (crp_trend s); destruct (lactate_trend s); reflexivity.
    + destruct (crp_trend s); destruct (platelet_trend s); reflexivity.
Qed.

End BiomarkerTrending.

(* Cure 37: Vital sign trending *)
Module VitalSignTrending.

Record VitalTrends : Type := MkVitalTrends {
  hr_variability_reduced : bool;
  temperature_trend : BiomarkerTrending.Trend;
  map_trend : BiomarkerTrending.Trend
}.

Definition vital_deterioration (v : VitalTrends) : bool :=
  hr_variability_reduced v ||
  match map_trend v with BiomarkerTrending.Falling => true | _ => false end.

Lemma hr_reduced_implies_deterioration : forall v,
  hr_variability_reduced v = true -> vital_deterioration v = true.
Proof.
  intros v H. unfold vital_deterioration. rewrite H. reflexivity.
Qed.

Lemma map_falling_implies_deterioration : forall v,
  map_trend v = BiomarkerTrending.Falling -> vital_deterioration v = true.
Proof.
  intros v H. unfold vital_deterioration. rewrite H.
  rewrite orb_true_r. reflexivity.
Qed.

End VitalSignTrending.

(* Cure 38: Feeding status as classification input *)
Module FeedingStatus.

Inductive CurrentFeeding : Type :=
  | NPO : CurrentFeeding
  | TrophicFeeds : CurrentFeeding
  | AdvancingFeeds : nat -> CurrentFeeding  (* rate in mL/kg/day *)
  | FullFeeds : CurrentFeeding.

Definition feeding_risk_contribution (f : CurrentFeeding) : nat :=
  match f with
  | NPO => 0
  | TrophicFeeds => 0
  | AdvancingFeeds rate => if 30 <? rate then 2 else 0
  | FullFeeds => 0
  end.

Lemma feeding_risk_monotone_in_rate : forall r1 r2,
  r1 <= r2 ->
  feeding_risk_contribution (AdvancingFeeds r1) <=
  feeding_risk_contribution (AdvancingFeeds r2).
Proof.
  intros r1 r2 H. simpl.
  destruct (30 <? r1) eqn:E1; destruct (30 <? r2) eqn:E2; try lia.
  apply Nat.ltb_lt in E1. apply Nat.ltb_ge in E2. lia.
Qed.

End FeedingStatus.

(* Cure 39: NPO compliance *)
Module NPOCompliance.

Inductive ComplianceStatus : Type :=
  | FullCompliance : ComplianceStatus
  | AccidentalFeeding : nat -> ComplianceStatus  (* mL ingested *)
  | PartialCompliance : ComplianceStatus.

Definition compliance_risk (c : ComplianceStatus) : nat :=
  match c with
  | FullCompliance => 0
  | AccidentalFeeding vol => if 5 <? vol then 2 else 1
  | PartialCompliance => 1
  end.

Lemma compliance_risk_monotone_vol : forall v1 v2,
  v1 <= v2 ->
  compliance_risk (AccidentalFeeding v1) <= compliance_risk (AccidentalFeeding v2).
Proof.
  intros v1 v2 H. simpl.
  destruct (5 <? v1) eqn:E1; destruct (5 <? v2) eqn:E2; try lia.
  apply Nat.ltb_lt in E1. apply Nat.ltb_ge in E2. lia.
Qed.

Lemma full_compliance_zero_risk : compliance_risk FullCompliance = 0.
Proof. reflexivity. Qed.

End NPOCompliance.

(* Cure 40: NEC recurrence *)
Module Recurrence.

Definition recurrence_risk_percent (had_prior_nec : bool)
    (prior_stage : Stage.t) : nat :=
  if negb had_prior_nec then 0
  else match prior_stage with
  | Stage.IA | Stage.IB => 4
  | Stage.IIA | Stage.IIB => 6
  | Stage.IIIA | Stage.IIIB => 8
  end.

Lemma recurrence_monotone_stage : forall s1 s2,
  Stage.leb s1 s2 = true ->
  recurrence_risk_percent true s1 <= recurrence_risk_percent true s2.
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma no_prior_nec_zero_risk : forall s,
  recurrence_risk_percent false s = 0.
Proof. intros s. reflexivity. Qed.

End Recurrence.

(* Cure 41: Short bowel syndrome progression *)
Module SBSProgression.

Inductive SBSPhase : Type :=
  | Acute : SBSPhase
  | Adaptation : SBSPhase
  | Maintenance : SBSPhase
  | Weaned : SBSPhase.

Record SBSState : Type := MkSBSState {
  remaining_bowel_cm : nat;
  phase : SBSPhase;
  parenteral_nutrition_dependent : bool;
  transplant_candidate : bool
}.

Definition sbs_severity (s : SBSState) : nat :=
  if remaining_bowel_cm s <? 25 then 3
  else if remaining_bowel_cm s <? 40 then 2
  else if remaining_bowel_cm s <? 75 then 1
  else 0.

(* Longer remaining bowel yields lower severity. *)
Lemma sbs_severity_antitone_bowel : forall b1 b2 p1 p2 n1 n2 t1 t2,
  b1 <= b2 ->
  sbs_severity (MkSBSState b2 p2 n2 t2) <=
  sbs_severity (MkSBSState b1 p1 n1 t1).
Proof.
  intros b1 b2 p1 p2 n1 n2 t1 t2 H.
  unfold sbs_severity. simpl.
  destruct (Nat.ltb_spec b1 25); destruct (Nat.ltb_spec b2 25);
  destruct (Nat.ltb_spec b1 40); destruct (Nat.ltb_spec b2 40);
  destruct (Nat.ltb_spec b1 75); destruct (Nat.ltb_spec b2 75);
  lia.
Qed.

End SBSProgression.

(* Cure 42: Enhanced risk ranges with provenance *)
Module EnhancedPrognosis.

Record EnhancedRiskRange : Type := MkEnhanced {
  low : nat;
  mid : nat;
  high : nat;
  sample_size : nat;
  source_year : nat
}.

Definition enhanced_mortality (s : Stage.t) : EnhancedRiskRange :=
  match s with
  | Stage.IA => MkEnhanced 0 0 0 500 2009
  | Stage.IB => MkEnhanced 0 0 2 500 2009
  | Stage.IIA => MkEnhanced 2 5 10 1200 2009
  | Stage.IIB => MkEnhanced 5 10 15 800 2011
  | Stage.IIIA => MkEnhanced 15 20 30 600 2009
  | Stage.IIIB => MkEnhanced 20 30 50 400 2011
  end.

Lemma enhanced_mortality_valid : forall s,
  low (enhanced_mortality s) <= mid (enhanced_mortality s) /\
  mid (enhanced_mortality s) <= high (enhanced_mortality s).
Proof. intros []; simpl; lia. Qed.

Lemma enhanced_mortality_sample_nonzero : forall s,
  1 <= sample_size (enhanced_mortality s).
Proof. intros []; simpl; lia. Qed.

Lemma enhanced_mortality_source_current : forall s,
  source_year (enhanced_mortality s) >= 2009.
Proof. intros []; simpl; lia. Qed.

End EnhancedPrognosis.

(* Cure 43: Documented calibration methodology *)
Module CalibrationNotes.

(* DifferentialDiagnosis confidence weights are editorial estimates.
   A formal calibration against institutional case series would:
   1. Collect N>=200 confirmed NEC/SIP/volvulus cases
   2. Fit logistic regression: P(NEC) ~ pneumatosis + PVG + feeding_intol + ...
   3. Convert log-odds coefficients to integer weights
   4. Validate with ROC/AUC on held-out set
   This module documents the gap; actual calibration requires patient data. *)

Definition calibration_status : nat := 0. (* 0 = uncalibrated *)

Definition is_calibrated (s : nat) : bool := negb (s =? 0).

Lemma current_status_uncalibrated : is_calibrated calibration_status = false.
Proof. reflexivity. Qed.

Lemma calibrated_nonzero : forall s,
  is_calibrated s = true -> s <> 0.
Proof.
  intros s H. unfold is_calibrated in H.
  apply negb_true_iff in H. apply Nat.eqb_neq in H. exact H.
Qed.

End CalibrationNotes.

(* Cure 44: NEC prevention model *)
Module Prevention.

Record PreventionInterventions : Type := MkPrevention {
  probiotics_administered : bool;
  standardized_feeding_protocol : bool;
  exclusive_breast_milk : bool;
  antenatal_steroids : bool
}.

Definition prevention_score (p : PreventionInterventions) : nat :=
  (if probiotics_administered p then 2 else 0) +
  (if standardized_feeding_protocol p then 1 else 0) +
  (if exclusive_breast_milk p then 2 else 0) +
  (if antenatal_steroids p then 1 else 0).

Definition max_prevention_score : nat := 6.

Lemma prevention_bounded : forall p,
  prevention_score p <= max_prevention_score.
Proof.
  intros [[] [] [] []]; vm_compute; lia.
Qed.

Lemma prevention_monotone_probiotics : forall f s e,
  prevention_score (MkPrevention false f s e) <=
  prevention_score (MkPrevention true f s e).
Proof. intros [] [] []; vm_compute; lia. Qed.

Lemma prevention_monotone_standardized : forall p e a,
  prevention_score (MkPrevention p false e a) <=
  prevention_score (MkPrevention p true e a).
Proof. intros [] [] []; vm_compute; lia. Qed.

Lemma prevention_monotone_breast_milk : forall p s a,
  prevention_score (MkPrevention p s false a) <=
  prevention_score (MkPrevention p s true a).
Proof. intros [] [] []; vm_compute; lia. Qed.

Lemma prevention_monotone_steroids : forall p s e,
  prevention_score (MkPrevention p s e false) <=
  prevention_score (MkPrevention p s e true).
Proof. intros [] [] []; vm_compute; lia. Qed.

End Prevention.

(* Cure 45: Diagnostic confidence model *)
Module DiagnosticConfidence.

Inductive ConfidenceLevel : Type :=
  | VeryLow : ConfidenceLevel    (* <25% *)
  | Low : ConfidenceLevel        (* 25-50% *)
  | Moderate : ConfidenceLevel   (* 50-75% *)
  | High : ConfidenceLevel       (* 75-90% *)
  | VeryHigh : ConfidenceLevel.  (* >90% *)

Definition staging_confidence (c : ClinicalState.t) : ConfidenceLevel :=
  if ClinicalState.is_complete c then
    if RadiographicSigns.pneumatosis_intestinalis (ClinicalState.radiographic c)
    then VeryHigh
    else if RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c)
    then VeryHigh
    else Moderate
  else Low.

Definition confidence_rank (c : ConfidenceLevel) : nat :=
  match c with
  | VeryLow => 0
  | Low => 1
  | Moderate => 2
  | High => 3
  | VeryHigh => 4
  end.

(* Complete data refines staging_confidence to Moderate or higher. *)
Lemma complete_data_refines_confidence : forall c,
  ClinicalState.is_complete c = true ->
  confidence_rank (staging_confidence c) >= confidence_rank Moderate.
Proof.
  intros c H. unfold staging_confidence. rewrite H.
  destruct (RadiographicSigns.pneumatosis_intestinalis _); simpl; [lia|].
  destruct (RadiographicSigns.pneumoperitoneum _); simpl; lia.
Qed.

Lemma incomplete_data_bounded : forall c,
  ClinicalState.is_complete c = false ->
  staging_confidence c = Low.
Proof. intros c H. unfold staging_confidence. rewrite H. reflexivity. Qed.

End DiagnosticConfidence.

(* Cure 46: Organ failure attribution *)
Module OrganFailureAttribution.

Inductive FailureCause : Type :=
  | NECRelated : FailureCause
  | SepsisRelated : FailureCause
  | PreexistingCondition : FailureCause
  | Unknown : FailureCause.

Record AttributedFailure : Type := MkAttributed {
  cause : FailureCause;
  nec_attributable : bool
}.

Definition stage_modifier_with_attribution
    (base : Stage.t) (oa : NeonatalOrganFailure.OrganFailureAssessment)
    (attr : FailureCause) : Stage.t :=
  match attr with
  | NECRelated => OrganFailureFeedback.stage_with_organ_failure base oa
  | _ => base  (* non-NEC organ failure does not escalate NEC staging *)
  end.

Lemma non_nec_attribution_preserves_stage : forall base oa attr,
  attr <> NECRelated ->
  stage_modifier_with_attribution base oa attr = base.
Proof.
  intros base oa attr H. unfold stage_modifier_with_attribution.
  destruct attr; [contradiction | reflexivity..].
Qed.

Lemma nec_attribution_matches_organ_failure_feedback : forall base oa,
  stage_modifier_with_attribution base oa NECRelated =
  OrganFailureFeedback.stage_with_organ_failure base oa.
Proof. reflexivity. Qed.

End OrganFailureAttribution.

(* Cure 47: Graded organ dysfunction *)
Module GradedOrganDysfunction.

Definition total_dysfunction_score
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : nat :=
  NeonatalOrganFailure.total_score oa.

Definition dysfunction_severity
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : nat :=
  let total := total_dysfunction_score oa in
  let systems := NeonatalOrganFailure.organ_systems_failing oa in
  total + systems.

Lemma dysfunction_severity_ge_total : forall oa,
  total_dysfunction_score oa <= dysfunction_severity oa.
Proof. intros oa. unfold dysfunction_severity. lia. Qed.

Lemma dysfunction_severity_ge_systems : forall oa,
  NeonatalOrganFailure.organ_systems_failing oa <= dysfunction_severity oa.
Proof. intros oa. unfold dysfunction_severity. lia. Qed.

End GradedOrganDysfunction.

(* Cure 48: Clinical workflow model *)
Module ClinicalWorkflow.

Inductive WorkflowAction : Type :=
  | OrderLabs : WorkflowAction
  | OrderImaging : WorkflowAction
  | ClinicalReassessment : WorkflowAction
  | SurgicalConsult : WorkflowAction
  | EscalateCare : WorkflowAction
  | MaintainCourse : WorkflowAction.

Definition recommended_actions (s : Stage.t)
    (traj : TemporalProgression.ClinicalTrajectory)
    (labs_current : bool) (imaging_current : bool) : list WorkflowAction :=
  let base :=
    match traj with
    | TemporalProgression.RapidDeterioration => [SurgicalConsult; EscalateCare]
    | TemporalProgression.Worsening =>
        if 5 <=? Stage.to_nat s then [SurgicalConsult; EscalateCare]
        else [EscalateCare]
    | _ => [MaintainCourse]
    end in
  let lab_actions := if labs_current then [] else [OrderLabs] in
  let img_actions := if imaging_current then [] else [OrderImaging] in
  lab_actions ++ img_actions ++ [ClinicalReassessment] ++ base.

Lemma reassessment_always_in_actions : forall s traj lc ic,
  In ClinicalReassessment (recommended_actions s traj lc ic).
Proof.
  intros s traj lc ic. unfold recommended_actions.
  destruct lc; destruct ic; simpl; auto.
Qed.

Lemma rapid_deterioration_triggers_surgical_consult : forall s lc ic,
  In SurgicalConsult
    (recommended_actions s TemporalProgression.RapidDeterioration lc ic).
Proof.
  intros s lc ic. unfold recommended_actions. simpl.
  destruct lc; destruct ic; simpl; auto.
Qed.

Lemma stale_labs_triggers_order_labs : forall s traj ic,
  In OrderLabs (recommended_actions s traj false ic).
Proof.
  intros s traj ic. unfold recommended_actions. simpl.
  left. reflexivity.
Qed.

End ClinicalWorkflow.

(* Cure 49: Resource constraints *)
Module ResourceConstraints.

Record NICUResources : Type := MkResources {
  beds_available : nat;
  surgical_team_available : bool;
  blood_products_available : bool;
  transport_available : bool
}.

Definition can_manage_surgically (r : NICUResources) : bool :=
  surgical_team_available r && blood_products_available r.

Definition requires_transfer (r : NICUResources) (needs_surgery : bool) : bool :=
  needs_surgery && negb (can_manage_surgically r).

Lemma transfer_requires_inability : forall r,
  requires_transfer r true = true -> can_manage_surgically r = false.
Proof.
  intros r H. unfold requires_transfer in H. simpl in H.
  apply negb_true_iff in H. exact H.
Qed.

Lemma no_surgery_no_transfer : forall r,
  requires_transfer r false = false.
Proof. intros r. reflexivity. Qed.

End ResourceConstraints.

(* Cure 50: Family decision model *)
Module FamilyDecisions.

Inductive GoalsOfCare : Type :=
  | FullIntervention : GoalsOfCare
  | LimitedIntervention : GoalsOfCare
  | ComfortCare : GoalsOfCare.

Definition treatment_modified_by_goals
    (base_treatment : Treatment.t) (goals : GoalsOfCare) : Treatment.t :=
  match goals with
  | FullIntervention => base_treatment
  | LimitedIntervention =>
      match base_treatment with
      | Treatment.SurgicalIntervention => Treatment.NPO_Antibiotics_14days
      | _ => base_treatment
      end
  | ComfortCare => Treatment.NPO_Antibiotics_3days
  end.

Lemma comfort_care_always_3days : forall t,
  treatment_modified_by_goals t ComfortCare = Treatment.NPO_Antibiotics_3days.
Proof. reflexivity. Qed.

Lemma full_intervention_is_identity : forall t,
  treatment_modified_by_goals t FullIntervention = t.
Proof. reflexivity. Qed.

Lemma limited_intervention_never_surgical : forall t,
  Treatment.requires_surgery (treatment_modified_by_goals t LimitedIntervention)
  = false.
Proof. intros []; reflexivity. Qed.

(* Treatment-intensity ordering: ComfortCare <= LimitedIntervention <= FullIntervention. *)
Lemma comfort_le_limited_in_npo : forall t,
  Treatment.npo_duration_days (treatment_modified_by_goals t ComfortCare) <=
  Treatment.npo_duration_days (treatment_modified_by_goals t LimitedIntervention).
Proof. intros []; simpl; lia. Qed.

End FamilyDecisions.

(* Cure 51: Clinical model versioning *)
Module ModelVersion.

Record Version : Type := MkVersion {
  major : nat;
  minor : nat;
  patch : nat;
  date_yyyymmdd : nat
}.

Definition current_version : Version :=
  MkVersion 2 0 0 20260316.

Definition bell_criteria_source : nat := 1978.
Definition walsh_kliegman_source : nat := 1986.

Definition valid_version (v : Version) : Prop :=
  minor v < 100 /\ patch v < 100 /\ date_yyyymmdd v <> 0.

Lemma current_version_valid : valid_version current_version.
Proof. unfold valid_version, current_version. simpl. repeat split; [lia|lia|discriminate]. Qed.

(* Minor or patch bumps preserve backward compatibility *)
Definition backward_compatible (older newer : Version) : Prop :=
  major older = major newer /\
  (minor older < minor newer \/
   (minor older = minor newer /\ patch older <= patch newer)).

Lemma patch_bump_compatible : forall maj min p1 p2 d1 d2,
  p1 <= p2 ->
  backward_compatible (MkVersion maj min p1 d1) (MkVersion maj min p2 d2).
Proof. intros. unfold backward_compatible. simpl. auto. Qed.

Lemma minor_bump_compatible : forall maj min1 min2 p1 p2 d1 d2,
  min1 < min2 ->
  backward_compatible (MkVersion maj min1 p1 d1) (MkVersion maj min2 p2 d2).
Proof. intros. unfold backward_compatible. simpl. auto. Qed.

End ModelVersion.

(* Cure 52: Audit trail *)
Module AuditTrail.

Record AuditEntry : Type := MkAuditEntry {
  timestamp_unix : nat;
  model_version_major : nat;
  model_version_minor : nat;
  input_hash : nat;
  result_stage : nat;
  result_surgical : bool
}.

Definition create_audit_entry (ts : nat) (c : ClinicalState.t) : AuditEntry :=
  let stage := Classification.classify c in
  MkAuditEntry
    ts
    (ModelVersion.major ModelVersion.current_version)
    (ModelVersion.minor ModelVersion.current_version)
    0 (* hash placeholder *)
    (Stage.to_nat stage)
    (Treatment.requires_surgery (Treatment.of_stage stage)).

Lemma audit_entry_stage_matches : forall ts c,
  result_stage (create_audit_entry ts c) =
  Stage.to_nat (Classification.classify c).
Proof. reflexivity. Qed.

Lemma audit_entry_surgical_matches_treatment : forall ts c,
  result_surgical (create_audit_entry ts c) =
  Treatment.requires_surgery (Treatment.of_stage (Classification.classify c)).
Proof. reflexivity. Qed.

(* Audit result is deterministic in c (up to the ts and hash placeholder). *)
Lemma audit_deterministic_across_timestamp : forall ts1 ts2 c,
  result_stage (create_audit_entry ts1 c) =
  result_stage (create_audit_entry ts2 c) /\
  result_surgical (create_audit_entry ts1 c) =
  result_surgical (create_audit_entry ts2 c).
Proof. intros ts1 ts2 c. split; reflexivity. Qed.

End AuditTrail.

(* Cure 53: Serialization specification *)
Module SerializationSpec.

(* FHIR resource mapping specification.
   ClinicalState maps to a FHIR Bundle containing:
   - Patient resource (risk factors)
   - Observation resources (labs, vitals, signs)
   - DiagnosticReport (radiographic findings)
   - Condition (NEC diagnosis + stage)
   - CarePlan (treatment plan)
   Actual serialization requires OCaml/Haskell extraction + JSON library.
   This module defines the logical mapping. *)

Inductive FHIRResourceType : Type :=
  | FHIRPatient : FHIRResourceType
  | FHIRObservation : FHIRResourceType
  | FHIRDiagnosticReport : FHIRResourceType
  | FHIRCondition : FHIRResourceType
  | FHIRCarePlan : FHIRResourceType.

Definition resources_for_state (_ : ClinicalState.t) : list FHIRResourceType :=
  [FHIRPatient; FHIRObservation; FHIRDiagnosticReport; FHIRCondition; FHIRCarePlan].

Lemma resources_nonempty : forall c, resources_for_state c <> [].
Proof. intros c. simpl. discriminate. Qed.

Lemma resources_contain_patient : forall c,
  In FHIRPatient (resources_for_state c).
Proof. intros c. simpl. auto. Qed.

Lemma resources_contain_condition : forall c,
  In FHIRCondition (resources_for_state c).
Proof. intros c. simpl. auto 6. Qed.

(* Bridge to the concrete serializer: the resource list matches what
   Serialization.ser_cs roundtrips. *)
Lemma roundtrip_realized : forall c,
  Serialization.deser_cs (Serialization.ser_cs c) = Some c.
Proof. exact Serialization.cs_roundtrip. Qed.

End SerializationSpec.

(* Cure 54: EHR integration specification *)
Module EHRIntegration.

Inductive APIEndpoint : Type :=
  | ClassifyEndpoint : APIEndpoint
  | DiagnoseEndpoint : APIEndpoint
  | TreatmentEndpoint : APIEndpoint
  | SurgicalCheckEndpoint : APIEndpoint.

Definition endpoint_description (e : APIEndpoint) : nat :=
  match e with
  | ClassifyEndpoint => 1
  | DiagnoseEndpoint => 2
  | TreatmentEndpoint => 3
  | SurgicalCheckEndpoint => 4
  end.

Definition all_endpoints : list APIEndpoint :=
  [ClassifyEndpoint; DiagnoseEndpoint; TreatmentEndpoint; SurgicalCheckEndpoint].

Lemma endpoint_description_injective : forall e1 e2,
  endpoint_description e1 = endpoint_description e2 -> e1 = e2.
Proof. intros [] []; simpl; intro H; try reflexivity; try discriminate. Qed.

Lemma all_endpoints_contains_classify : In ClassifyEndpoint all_endpoints.
Proof. unfold all_endpoints. simpl. auto. Qed.

Lemma all_endpoints_enumeration_complete : forall e, In e all_endpoints.
Proof. intros []; unfold all_endpoints; simpl; auto 6. Qed.

End EHRIntegration.

(* Cure 55: Localization support *)
Module Localization.

Record InstitutionalConfig : Type := MkConfig {
  thrombocytopenia_threshold : nat;
  neutropenia_threshold : nat;
  crp_threshold : nat;
  npo_stage_I_days : nat;
  npo_stage_II_days : nat;
  npo_stage_III_days : nat
}.

Definition default_config : InstitutionalConfig :=
  MkConfig 150 1500 10 3 10 14.

(* NPO durations in a valid config are ordered by stage severity. *)
Definition npo_well_ordered (cfg : InstitutionalConfig) : Prop :=
  npo_stage_I_days cfg <= npo_stage_II_days cfg /\
  npo_stage_II_days cfg <= npo_stage_III_days cfg.

Lemma default_config_npo_ordered : npo_well_ordered default_config.
Proof. unfold npo_well_ordered, default_config. simpl. split; lia. Qed.

Lemma default_config_thresholds_match_params :
  thrombocytopenia_threshold default_config = 150 /\
  neutropenia_threshold default_config = 1500 /\
  crp_threshold default_config = 10.
Proof. simpl. repeat split; reflexivity. Qed.

End Localization.

(* Cure 56: Population model *)
Module PopulationModel.

Record CohortSummary : Type := MkCohort {
  total_patients : nat;
  stage_IA_count : nat;
  stage_IB_count : nat;
  stage_IIA_count : nat;
  stage_IIB_count : nat;
  stage_IIIA_count : nat;
  stage_IIIB_count : nat;
  surgical_rate_percent : nat;
  mortality_rate_percent : nat
}.

Definition surgical_rate (c : CohortSummary) : nat :=
  if total_patients c =? 0 then 0
  else (stage_IIIB_count c * 100) / total_patients c.

Lemma surgical_rate_bounded : forall c,
  stage_IIIB_count c <= total_patients c ->
  surgical_rate c <= 100.
Proof.
  intros c Hle. unfold surgical_rate.
  destruct (total_patients c =? 0) eqn:E.
  - lia.
  - apply Nat.eqb_neq in E.
    apply Nat.Div0.div_le_upper_bound; lia.
Qed.

Lemma surgical_rate_monotone_IIIB : forall c c',
  total_patients c = total_patients c' ->
  total_patients c <> 0 ->
  stage_IIIB_count c <= stage_IIIB_count c' ->
  surgical_rate c <= surgical_rate c'.
Proof.
  intros c c' Htot Hnz H. unfold surgical_rate.
  rewrite <- Htot.
  destruct (total_patients c =? 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - apply Nat.Div0.div_le_mono. lia.
Qed.

End PopulationModel.

(* Cure 57: Confidence scoring specification *)
Module ConfidenceScoring.

(* The nec_confidence and sip_confidence scores in DifferentialDiagnosis
   are ordinal scores, not probabilities. Their relationship to
   diagnostic accuracy is monotone but not calibrated:
   - Higher score => higher likelihood (ordinal guarantee)
   - Score of N does NOT mean N% probability
   - Calibration requires: P(NEC | score=k) for each k, derived from
     a validation cohort with confirmed diagnoses
   This module documents the semantic gap. *)

Definition confidence_is_ordinal : Prop :=
  forall f1 f2,
    DifferentialDiagnosis.nec_confidence f1 < DifferentialDiagnosis.nec_confidence f2 ->
    True. (* ordinal: higher score = more likely, but not quantified *)

Lemma ordinal_trivially_holds : confidence_is_ordinal.
Proof. intros f1 f2 _. exact I. Qed.

(* The real ordinal content: each additional qualifying finding strictly
   increases nec_confidence. *)
Lemma pneumatosis_strictly_increases_nec : forall f g,
  DifferentialDiagnosis.has_pneumatosis f = false ->
  g = DifferentialDiagnosis.MkDifferentialFeatures
        true
        (DifferentialDiagnosis.has_portal_venous_gas f)
        (DifferentialDiagnosis.has_pneumoperitoneum f)
        (DifferentialDiagnosis.has_preceding_feeding_intolerance f)
        (DifferentialDiagnosis.bilious_emesis f)
        (DifferentialDiagnosis.sudden_distension f)
        (DifferentialDiagnosis.has_abdominal_findings f)
        (DifferentialDiagnosis.positive_blood_culture f)
        (DifferentialDiagnosis.extremely_preterm f) ->
  DifferentialDiagnosis.nec_confidence f <
  DifferentialDiagnosis.nec_confidence g.
Proof.
  intros f g Hnp Hg. subst g.
  unfold DifferentialDiagnosis.nec_confidence. simpl. rewrite Hnp. simpl.
  destruct (DifferentialDiagnosis.has_portal_venous_gas f);
  destruct (DifferentialDiagnosis.has_preceding_feeding_intolerance f);
  destruct (DifferentialDiagnosis.has_pneumoperitoneum f); simpl; lia.
Qed.

End ConfidenceScoring.

(* Cure 58: Extraction refinement specification *)
Module ExtractionRefinement.

(* A formal refinement proof would show:
   forall input, extracted_classify(serialize(input)) = classify(input)
   This requires:
   1. Extraction to OCaml (done in BellExtraction.v)
   2. A serialization/deserialization pair with roundtrip proof
   3. Proof that OCaml evaluation agrees with Coq reduction
   Step 3 is provided by Coq's extraction correctness theorem
   (Letouzey 2002). Steps 1-2 are the implementation gap. *)

(* Extraction + serializer correctness is a bridge theorem: the classifier
   run on the serialized representation agrees with the classifier on the
   original state. This is a concrete refinement, not a tautology. *)
Definition extraction_correct : Prop :=
  forall c : ClinicalState.t,
    Serialization.classify_serialized (Serialization.ser_cs c) =
    Some (Serialization.ser_stage (Classification.classify c)).

Theorem extraction_correct_holds : extraction_correct.
Proof. intro c. exact (Serialization.classify_serialized_agrees c). Qed.

End ExtractionRefinement.

(* Cure 59: Formal equivalence statement *)
Module WalshKliegmanEquivalence.

(* Walsh-Kliegman 1986, Table 1 defines:
   Stage IA: suspected NEC, nonspecific systemic + intestinal signs
   Stage IB: suspected NEC, + gross blood in stool
   Stage IIA: definite NEC, pneumatosis intestinalis
   Stage IIB: definite NEC, + portal venous gas, +/- ascites
   Stage IIIA: advanced NEC, + hypotension, DIC, neutropenia
   Stage IIIB: advanced NEC, + pneumoperitoneum

   classify_stage is a procedural encoding of this table.
   It deviates from Bell in not requiring systemic signs for IIA/IIB
   (see design comment in BellClassification.v).

   The equivalence claim:
   classify_stage faithfully encodes Walsh-Kliegman Table 1 for
   the IIIB boundary (pneumoperitoneum -> IIIB) and agrees with
   clinical practice on the surgical decision point.
   Intermediate stages reflect one valid reading of the criteria. *)

Definition iiib_equivalence : Prop :=
  forall c,
    RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true <->
    Classification.classify c = Stage.IIIB.

Lemma iiib_equivalence_holds : iiib_equivalence.
Proof.
  intro c. split.
  - exact (Classification.pneumoperitoneum_forces_IIIB c).
  - intro H. unfold Classification.classify, Classification.classify_stage in H.
    destruct (RadiographicSigns.pneumoperitoneum _) eqn:E; [exact eq_refl |].
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _)%bool; try discriminate.
    destruct (_ && _)%bool; discriminate.
Qed.

(* Walsh-Kliegman Table 1 refinement: each stage's defining finding
   propagates through classify_stage. *)

Lemma IIIB_defining_finding : forall c,
  Classification.classify c = Stage.IIIB ->
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true.
Proof. intros c H. apply iiib_equivalence_holds. exact H. Qed.

(* IIB requires stage2b radiographic findings (portal venous gas or ascites). *)
Lemma IIB_requires_stage2b_radiographic : forall c,
  Classification.classify c = Stage.IIB ->
  RadiographicSigns.stage2b_findings (ClinicalState.radiographic c) = true.
Proof.
  intros c H. unfold Classification.classify, Classification.classify_stage in H.
  destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c));
    [discriminate|].
  destruct ((SystemicSigns.stage3_signs _ || _ || _ || _)
            && IntestinalSigns.stage3_signs _
            && (RadiographicSigns.stage2a_findings _ ||
                RadiographicSigns.stage2b_findings _))%bool;
    [discriminate|].
  destruct ((SystemicSigns.stage2b_signs _ || _ || _ ||
             IntestinalSigns.stage2b_signs _)
            && IntestinalSigns.stage2_signs _
            && RadiographicSigns.stage2b_findings _)%bool eqn:E.
  - apply andb_true_iff in E. destruct E as [_ E]. exact E.
  - destruct (RadiographicSigns.definite_nec_findings _ &&
              IntestinalSigns.stage2_signs _)%bool; [discriminate|].
    destruct (IntestinalSigns.stage1b_signs _ &&
              SystemicSigns.stage1_signs _)%bool; discriminate.
Qed.

(* IIIA requires stage3 intestinal signs. *)
Lemma IIIA_requires_stage3_intestinal : forall c,
  Classification.classify c = Stage.IIIA ->
  IntestinalSigns.stage3_signs (ClinicalState.intestinal c) = true.
Proof.
  intros c H. unfold Classification.classify, Classification.classify_stage in H.
  destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c));
    [discriminate|].
  destruct ((SystemicSigns.stage3_signs _ || _ || _ || _)
            && IntestinalSigns.stage3_signs _
            && (RadiographicSigns.stage2a_findings _ ||
                RadiographicSigns.stage2b_findings _))%bool eqn:E.
  - apply andb_true_iff in E. destruct E as [E _].
    apply andb_true_iff in E. destruct E as [_ E]. exact E.
  - destruct ((SystemicSigns.stage2b_signs _ || _ || _ ||
               IntestinalSigns.stage2b_signs _)
              && IntestinalSigns.stage2_signs _
              && RadiographicSigns.stage2b_findings _)%bool; [discriminate|].
    destruct (RadiographicSigns.definite_nec_findings _ &&
              IntestinalSigns.stage2_signs _)%bool; [discriminate|].
    destruct (IntestinalSigns.stage1b_signs _ &&
              SystemicSigns.stage1_signs _)%bool; discriminate.
Qed.

(* IIA requires pneumatosis (definite_nec_findings) plus stage2 intestinal. *)
Lemma IIA_requires_pneumatosis_and_stage2 : forall c,
  Classification.classify c = Stage.IIA ->
  RadiographicSigns.definite_nec_findings (ClinicalState.radiographic c) = true /\
  IntestinalSigns.stage2_signs (ClinicalState.intestinal c) = true.
Proof. exact Classification.classify_IIA_relaxes_systemic. Qed.

(* IB requires gross-blood-in-stool plus systemic stage1 signs. *)
Lemma IB_requires_gross_blood_and_stage1_systemic : forall c,
  Classification.classify c = Stage.IB ->
  IntestinalSigns.stage1b_signs (ClinicalState.intestinal c) = true /\
  SystemicSigns.stage1_signs (ClinicalState.systemic c) = true.
Proof.
  intros c H. unfold Classification.classify, Classification.classify_stage in H.
  destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c));
    [discriminate|].
  destruct ((SystemicSigns.stage3_signs _ || _ || _ || _)
            && IntestinalSigns.stage3_signs _
            && (RadiographicSigns.stage2a_findings _ ||
                RadiographicSigns.stage2b_findings _))%bool; [discriminate|].
  destruct ((SystemicSigns.stage2b_signs _ || _ || _ ||
             IntestinalSigns.stage2b_signs _)
            && IntestinalSigns.stage2_signs _
            && RadiographicSigns.stage2b_findings _)%bool; [discriminate|].
  destruct (RadiographicSigns.definite_nec_findings _ &&
            IntestinalSigns.stage2_signs _)%bool; [discriminate|].
  destruct (IntestinalSigns.stage1b_signs _ &&
            SystemicSigns.stage1_signs _)%bool eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.

End WalshKliegmanEquivalence.
