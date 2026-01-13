(******************************************************************************)
(*                                                                            *)
(*                  Bell Staging for Necrotizing Enterocolitis                *)
(*                                                                            *)
(*     Formalization of modified Bell staging criteria for NEC in neonates:   *)
(*     Stage I (suspected), Stage II (definite), Stage III (advanced).        *)
(*     Clinical signs, radiographic findings, and systemic manifestations.    *)
(*     Decision predicates for staging and surgical intervention triggers.    *)
(*                                                                            *)
(*     "I will stand at my watch and station myself on the ramparts; I will   *)
(*     look to see what he will say to me."                                   *)
(*     - Habakkuk 2:1                                                         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Lia.

Import ListNotations.

Module ClinicalParameters.

Record ClinicalParam : Type := MkParam {
  param_value : nat;
  param_source : nat;
  param_year : nat
}.

Definition bell_1978 : nat := 1.
Definition walsh_kliegman_1986 : nat := 2.
Definition neu_walker_2011 : nat := 3.
Definition patel_2015 : nat := 4.
Definition gephart_2012 : nat := 5.

Definition extremely_preterm_threshold :=
  MkParam 28 walsh_kliegman_1986 1986.

Definition elbw_threshold :=
  MkParam 1000 walsh_kliegman_1986 1986.

Definition vlbw_threshold :=
  MkParam 1500 walsh_kliegman_1986 1986.

Definition thrombocytopenia_threshold :=
  MkParam 150 walsh_kliegman_1986 1986.

Definition severe_thrombocytopenia_threshold :=
  MkParam 50 patel_2015 2015.

Definition pneumatosis_pathognomonic :=
  MkParam 1 bell_1978 1978.

Definition portal_venous_gas_pathognomonic :=
  MkParam 1 bell_1978 1978.

Definition pneumoperitoneum_requires_surgery :=
  MkParam 1 bell_1978 1978.

Definition npo_duration_stage_I :=
  MkParam 3 walsh_kliegman_1986 1986.

Definition npo_duration_stage_II :=
  MkParam 10 walsh_kliegman_1986 1986.

Definition npo_duration_stage_III :=
  MkParam 14 walsh_kliegman_1986 1986.

Definition breast_milk_protective :=
  MkParam 1 neu_walker_2011 2011.

End ClinicalParameters.

Module RiskFactors.

Record t : Type := MkRiskFactors {
  gestational_age_weeks : nat;
  birth_weight_grams : nat;
  formula_fed : bool;
  history_of_perinatal_asphyxia : bool;
  congenital_heart_disease : bool;
  polycythemia : bool;
  umbilical_catheter : bool;
  exchange_transfusion : bool
}.

Definition extremely_preterm (r : t) : bool :=
  gestational_age_weeks r <? 28.

Definition very_preterm (r : t) : bool :=
  (28 <=? gestational_age_weeks r) && (gestational_age_weeks r <? 32).

Definition moderate_preterm (r : t) : bool :=
  (32 <=? gestational_age_weeks r) && (gestational_age_weeks r <? 37).

Definition term (r : t) : bool :=
  37 <=? gestational_age_weeks r.

Definition extremely_low_birth_weight (r : t) : bool :=
  birth_weight_grams r <? 1000.

Definition very_low_birth_weight (r : t) : bool :=
  (1000 <=? birth_weight_grams r) && (birth_weight_grams r <? 1500).

Definition low_birth_weight (r : t) : bool :=
  (1500 <=? birth_weight_grams r) && (birth_weight_grams r <? 2500).

Definition risk_score (r : t) : nat :=
  (if extremely_preterm r then 4
   else if very_preterm r then 3
   else if moderate_preterm r then 2
   else 0) +
  (if extremely_low_birth_weight r then 4
   else if very_low_birth_weight r then 3
   else if low_birth_weight r then 1
   else 0) +
  (if formula_fed r then 1 else 0) +
  (if history_of_perinatal_asphyxia r then 2 else 0) +
  (if congenital_heart_disease r then 2 else 0) +
  (if polycythemia r then 1 else 0) +
  (if umbilical_catheter r then 1 else 0) +
  (if exchange_transfusion r then 1 else 0).

Definition high_risk (r : t) : bool :=
  6 <=? risk_score r.

Lemma extremely_preterm_high_risk : forall r,
  extremely_preterm r = true ->
  extremely_low_birth_weight r = true ->
  high_risk r = true.
Proof.
  intros r Hp Hw. unfold high_risk, risk_score.
  rewrite Hp, Hw. simpl.
  reflexivity.
Qed.

End RiskFactors.

Module LabValues.

Record t : Type := MkLabValues {
  wbc_k_per_uL : nat;
  absolute_neutrophil_count : nat;
  platelet_k_per_uL : nat;
  crp_mg_L : nat;
  procalcitonin_ng_mL_x10 : nat;
  lactate_mmol_L_x10 : nat;
  ph_x100 : nat;
  base_deficit : nat;
  pco2_mmHg : nat;
  glucose_mg_dL : nat
}.

Definition leukopenia (l : t) : bool :=
  wbc_k_per_uL l <? 5.

Definition leukocytosis (l : t) : bool :=
  25 <? wbc_k_per_uL l.

Definition neutropenia (l : t) : bool :=
  absolute_neutrophil_count l <? 1500.

Definition thrombocytopenia (l : t) : bool :=
  platelet_k_per_uL l <? 150.

Definition severe_thrombocytopenia (l : t) : bool :=
  platelet_k_per_uL l <? 50.

Definition elevated_crp (l : t) : bool :=
  10 <? crp_mg_L l.

Definition elevated_procalcitonin (l : t) : bool :=
  5 <? procalcitonin_ng_mL_x10 l.

Definition elevated_lactate (l : t) : bool :=
  20 <? lactate_mmol_L_x10 l.

Definition metabolic_acidosis (l : t) : bool :=
  (ph_x100 l <? 735) && (6 <? base_deficit l).

Definition respiratory_acidosis (l : t) : bool :=
  (ph_x100 l <? 735) && (45 <? pco2_mmHg l).

Definition hypoglycemia (l : t) : bool :=
  glucose_mg_dL l <? 45.

Definition hyperglycemia (l : t) : bool :=
  180 <? glucose_mg_dL l.

Definition dic_likely (l : t) : bool :=
  severe_thrombocytopenia l && elevated_lactate l.

Definition sepsis_markers_elevated (l : t) : bool :=
  elevated_crp l || elevated_procalcitonin l.

Definition lab_severity_score (l : t) : nat :=
  (if leukopenia l || leukocytosis l then 1 else 0) +
  (if neutropenia l then 2 else 0) +
  (if thrombocytopenia l then 1 else 0) +
  (if severe_thrombocytopenia l then 2 else 0) +
  (if elevated_crp l then 1 else 0) +
  (if elevated_lactate l then 2 else 0) +
  (if metabolic_acidosis l then 2 else 0) +
  (if dic_likely l then 3 else 0).

Lemma dic_requires_severe_thrombocytopenia : forall l,
  dic_likely l = true -> severe_thrombocytopenia l = true.
Proof.
  intros l H. unfold dic_likely in H.
  apply andb_true_iff in H. destruct H as [H1 _]. exact H1.
Qed.

End LabValues.

Module Antibiotics.

Inductive Agent : Type :=
  | Ampicillin : Agent
  | Gentamicin : Agent
  | Metronidazole : Agent
  | Vancomycin : Agent
  | Cefotaxime : Agent
  | Meropenem : Agent
  | Piperacillin_Tazobactam : Agent.

Inductive Regimen : Type :=
  | Empiric_AmpGent : Regimen
  | Empiric_AmpGentMetro : Regimen
  | Broad_VancCefotaximeMetro : Regimen
  | Broad_VancMeropenem : Regimen
  | Broad_PipTazo : Regimen.

Definition agents_in_regimen (r : Regimen) : list Agent :=
  match r with
  | Empiric_AmpGent => [Ampicillin; Gentamicin]
  | Empiric_AmpGentMetro => [Ampicillin; Gentamicin; Metronidazole]
  | Broad_VancCefotaximeMetro => [Vancomycin; Cefotaxime; Metronidazole]
  | Broad_VancMeropenem => [Vancomycin; Meropenem]
  | Broad_PipTazo => [Piperacillin_Tazobactam]
  end.

Definition has_anaerobic_coverage (r : Regimen) : bool :=
  match r with
  | Empiric_AmpGent => false
  | Empiric_AmpGentMetro => true
  | Broad_VancCefotaximeMetro => true
  | Broad_VancMeropenem => true
  | Broad_PipTazo => true
  end.

Definition has_gram_negative_coverage (r : Regimen) : bool :=
  match r with
  | Empiric_AmpGent => true
  | Empiric_AmpGentMetro => true
  | Broad_VancCefotaximeMetro => true
  | Broad_VancMeropenem => true
  | Broad_PipTazo => true
  end.

Definition recommended_regimen_by_stage (stage_nat : nat) : Regimen :=
  match stage_nat with
  | 1 | 2 => Empiric_AmpGent
  | 3 | 4 => Empiric_AmpGentMetro
  | _ => Broad_VancMeropenem
  end.

Definition duration_days (stage_nat : nat) : nat :=
  match stage_nat with
  | 1 | 2 => 3
  | 3 | 4 => 10
  | _ => 14
  end.

Lemma advanced_nec_has_anaerobic_coverage : forall n,
  5 <= n ->
  has_anaerobic_coverage (recommended_regimen_by_stage n) = true.
Proof.
  intros n H. unfold recommended_regimen_by_stage.
  destruct n as [|[|[|[|[|n']]]]]; simpl; try lia; reflexivity.
Qed.

End Antibiotics.

Module FeedingProtocol.

Inductive FeedingStatus : Type :=
  | NPO : FeedingStatus
  | TrophicFeeds : FeedingStatus
  | AdvancingFeeds : FeedingStatus
  | FullFeeds : FeedingStatus.

Inductive FeedType : Type :=
  | BreastMilk : FeedType
  | DonorMilk : FeedType
  | Preterm_Formula : FeedType
  | Elemental_Formula : FeedType.

Record FeedingState : Type := MkFeedingState {
  current_status : FeedingStatus;
  current_feed_type : option FeedType;
  days_npo : nat;
  ml_per_kg_per_day : nat
}.

Definition npo_duration_by_stage (stage_nat : nat) : nat :=
  match stage_nat with
  | 1 | 2 => 3
  | 3 | 4 => 7
  | 5 => 14
  | _ => 14
  end.

Definition can_restart_feeds (stage_nat : nat) (days_npo : nat)
    (abdominal_exam_normal : bool) (no_bilious_residuals : bool) : bool :=
  (npo_duration_by_stage stage_nat <=? days_npo) &&
  abdominal_exam_normal && no_bilious_residuals.

Definition trophic_feed_volume_ml_kg_day : nat := 20.
Definition advancement_rate_ml_kg_day : nat := 20.
Definition full_feed_volume_ml_kg_day : nat := 150.

Definition preferred_feed_type_post_nec : FeedType := BreastMilk.

Definition days_to_full_feeds (start_volume : nat) : nat :=
  (full_feed_volume_ml_kg_day - start_volume) / advancement_rate_ml_kg_day.

Lemma breast_milk_preferred :
  preferred_feed_type_post_nec = BreastMilk.
Proof. reflexivity. Qed.

Lemma stage_IIIB_requires_14_days_npo :
  npo_duration_by_stage 6 = 14.
Proof. reflexivity. Qed.

End FeedingProtocol.

Module TemporalProgression.

Inductive ClinicalTrajectory : Type :=
  | Stable : ClinicalTrajectory
  | Improving : ClinicalTrajectory
  | Worsening : ClinicalTrajectory
  | RapidDeterioration : ClinicalTrajectory.

Inductive ManagementPhase : Type :=
  | Recognition : ManagementPhase
  | Stabilization : ManagementPhase
  | ActiveTreatment : ManagementPhase
  | SurgicalEvaluation : ManagementPhase
  | PostOperative : ManagementPhase
  | Recovery : ManagementPhase
  | Resolved : ManagementPhase.

Definition phase_to_nat (p : ManagementPhase) : nat :=
  match p with
  | Recognition => 1
  | Stabilization => 2
  | ActiveTreatment => 3
  | SurgicalEvaluation => 4
  | PostOperative => 5
  | Recovery => 6
  | Resolved => 7
  end.

Record TimePoint : Type := MkTimePoint {
  hours_since_onset : nat;
  current_phase : ManagementPhase;
  trajectory : ClinicalTrajectory;
  stage_at_timepoint : nat
}.

Definition valid_transition (from to : ManagementPhase) : bool :=
  match from, to with
  | Recognition, Stabilization => true
  | Stabilization, ActiveTreatment => true
  | ActiveTreatment, SurgicalEvaluation => true
  | ActiveTreatment, Recovery => true
  | SurgicalEvaluation, PostOperative => true
  | SurgicalEvaluation, ActiveTreatment => true
  | PostOperative, Recovery => true
  | Recovery, Resolved => true
  | p1, p2 => phase_to_nat p1 =? phase_to_nat p2
  end.

Definition deterioration_triggers_escalation (t : ClinicalTrajectory) : bool :=
  match t with
  | Worsening => true
  | RapidDeterioration => true
  | _ => false
  end.

Definition hours_to_reassess (phase : ManagementPhase) (traj : ClinicalTrajectory) : nat :=
  match traj with
  | RapidDeterioration => 2
  | Worsening => 4
  | Stable => 6
  | Improving => 12
  end.

Lemma rapid_deterioration_frequent_reassess :
  hours_to_reassess ActiveTreatment RapidDeterioration = 2.
Proof. reflexivity. Qed.

Lemma transition_recognition_to_stabilization :
  valid_transition Recognition Stabilization = true.
Proof. reflexivity. Qed.

Definition is_terminal_phase (p : ManagementPhase) : bool :=
  match p with
  | Resolved => true
  | _ => false
  end.

End TemporalProgression.

Module Stage.

Inductive t : Type :=
  | IA : t
  | IB : t
  | IIA : t
  | IIB : t
  | IIIA : t
  | IIIB : t.

Definition to_nat (s : t) : nat :=
  match s with
  | IA => 1
  | IB => 2
  | IIA => 3
  | IIB => 4
  | IIIA => 5
  | IIIB => 6
  end.

Definition le (s1 s2 : t) : Prop :=
  to_nat s1 <= to_nat s2.

Definition leb (s1 s2 : t) : bool :=
  to_nat s1 <=? to_nat s2.

Lemma to_nat_lower_bound : forall s, 1 <= to_nat s.
Proof. intros []; simpl; lia. Qed.

Lemma to_nat_upper_bound : forall s, to_nat s <= 6.
Proof. intros []; simpl; lia. Qed.

End Stage.

Module Diagnosis.

Inductive t : Type :=
  | NotNEC : t
  | SuspectedSIP : t
  | SuspectedNEC : Stage.t -> t
  | ConfirmedNEC : Stage.t -> t.

Definition is_nec (d : t) : bool :=
  match d with
  | SuspectedNEC _ | ConfirmedNEC _ => true
  | _ => false
  end.

Definition is_sip (d : t) : bool :=
  match d with
  | SuspectedSIP => true
  | _ => false
  end.

Definition stage_of (d : t) : option Stage.t :=
  match d with
  | NotNEC => None
  | SuspectedSIP => None
  | SuspectedNEC s => Some s
  | ConfirmedNEC s => Some s
  end.

Definition is_confirmed (d : t) : bool :=
  match d with
  | ConfirmedNEC _ => true
  | _ => false
  end.

Definition requires_surgery (d : t) : bool :=
  match d with
  | SuspectedSIP => true
  | ConfirmedNEC Stage.IIIB => true
  | _ => false
  end.

End Diagnosis.

Module SystemicSigns.

Record t : Type := MkSystemicSigns {
  temperature_instability : bool;
  apnea : bool;
  bradycardia : bool;
  lethargy : bool;
  metabolic_acidosis : bool;
  thrombocytopenia : bool;
  hypotension : bool;
  respiratory_failure : bool;
  dic : bool;
  neutropenia : bool
}.

Definition none : t :=
  MkSystemicSigns false false false false false false false false false false.

Definition stage1_signs (s : t) : bool :=
  temperature_instability s || apnea s || bradycardia s || lethargy s.

Definition stage2b_signs (s : t) : bool :=
  metabolic_acidosis s || thrombocytopenia s.

Definition stage3_signs (s : t) : bool :=
  hypotension s || respiratory_failure s || dic s || neutropenia s.

Definition severity_score (s : t) : nat :=
  (if temperature_instability s then 1 else 0) +
  (if apnea s then 1 else 0) +
  (if bradycardia s then 1 else 0) +
  (if lethargy s then 1 else 0) +
  (if metabolic_acidosis s then 2 else 0) +
  (if thrombocytopenia s then 2 else 0) +
  (if hypotension s then 3 else 0) +
  (if respiratory_failure s then 3 else 0) +
  (if dic s then 3 else 0) +
  (if neutropenia s then 3 else 0).

Lemma severity_score_max : forall s, severity_score s <= 20.
Proof.
  intros s. unfold severity_score.
  destruct (temperature_instability s); destruct (apnea s);
  destruct (bradycardia s); destruct (lethargy s);
  destruct (metabolic_acidosis s); destruct (thrombocytopenia s);
  destruct (hypotension s); destruct (respiratory_failure s);
  destruct (dic s); destruct (neutropenia s); simpl; lia.
Qed.

End SystemicSigns.

Module IntestinalSigns.

Record t : Type := MkIntestinalSigns {
  elevated_gastric_residuals : bool;
  mild_abdominal_distension : bool;
  occult_blood_in_stool : bool;
  gross_blood_in_stool : bool;
  absent_bowel_sounds : bool;
  abdominal_tenderness : bool;
  abdominal_cellulitis : bool;
  right_lower_quadrant_mass : bool;
  marked_distension : bool;
  peritonitis : bool
}.

Definition none : t :=
  MkIntestinalSigns false false false false false false false false false false.

Definition stage1a_signs (s : t) : bool :=
  elevated_gastric_residuals s || mild_abdominal_distension s || occult_blood_in_stool s.

Definition stage1b_signs (s : t) : bool :=
  gross_blood_in_stool s.

Definition stage2_signs (s : t) : bool :=
  absent_bowel_sounds s || abdominal_tenderness s.

Definition stage2b_signs (s : t) : bool :=
  abdominal_cellulitis s || right_lower_quadrant_mass s.

Definition stage3_signs (s : t) : bool :=
  marked_distension s || peritonitis s.

End IntestinalSigns.

Module RadiographicSigns.

Record t : Type := MkRadiographicSigns {
  normal_or_mild_ileus : bool;
  intestinal_dilation : bool;
  focal_ileus : bool;
  pneumatosis_intestinalis : bool;
  portal_venous_gas : bool;
  ascites : bool;
  pneumoperitoneum : bool
}.

Definition none : t :=
  MkRadiographicSigns false false false false false false false.

Definition normal_variant : t :=
  MkRadiographicSigns true false false false false false false.

Definition stage1_findings (r : t) : bool :=
  normal_or_mild_ileus r.

Definition stage2a_findings (r : t) : bool :=
  intestinal_dilation r || focal_ileus r || pneumatosis_intestinalis r.

Definition stage2b_findings (r : t) : bool :=
  portal_venous_gas r || ascites r.

Definition stage3b_findings (r : t) : bool :=
  pneumoperitoneum r.

Definition definite_nec_findings (r : t) : bool :=
  pneumatosis_intestinalis r.

Lemma pneumoperitoneum_implies_stage3b : forall r,
  pneumoperitoneum r = true -> stage3b_findings r = true.
Proof. intros r H. unfold stage3b_findings. exact H. Qed.

End RadiographicSigns.

Module ClinicalState.

Record t : Type := MkClinicalState {
  risk_factors : RiskFactors.t;
  labs : LabValues.t;
  systemic : SystemicSigns.t;
  intestinal : IntestinalSigns.t;
  radiographic : RadiographicSigns.t;
  hours_since_symptom_onset : nat
}.

Definition default_risk_factors : RiskFactors.t :=
  RiskFactors.MkRiskFactors 40 3500 false false false false false false.

Definition default_labs : LabValues.t :=
  LabValues.MkLabValues 10 5000 200 5 2 15 740 0 40 80.

Definition empty : t :=
  MkClinicalState
    default_risk_factors
    default_labs
    SystemicSigns.none
    IntestinalSigns.none
    RadiographicSigns.none
    0.

Definition is_high_risk_patient (c : t) : bool :=
  RiskFactors.high_risk (risk_factors c).

Definition has_lab_derangements (c : t) : bool :=
  LabValues.sepsis_markers_elevated (labs c) ||
  LabValues.thrombocytopenia (labs c) ||
  LabValues.metabolic_acidosis (labs c).

Definition overall_severity_score (c : t) : nat :=
  RiskFactors.risk_score (risk_factors c) +
  LabValues.lab_severity_score (labs c) +
  SystemicSigns.severity_score (systemic c).

End ClinicalState.

Module Classification.

Definition has_any_findings (c : ClinicalState.t) : bool :=
  let sys := ClinicalState.systemic c in
  let int := ClinicalState.intestinal c in
  let rad := ClinicalState.radiographic c in
  SystemicSigns.stage1_signs sys ||
  IntestinalSigns.stage1a_signs int ||
  IntestinalSigns.stage1b_signs int ||
  RadiographicSigns.definite_nec_findings rad ||
  RadiographicSigns.stage2b_findings rad ||
  RadiographicSigns.pneumoperitoneum rad.

Definition classify_stage (c : ClinicalState.t) : Stage.t :=
  let sys := ClinicalState.systemic c in
  let int := ClinicalState.intestinal c in
  let rad := ClinicalState.radiographic c in
  if RadiographicSigns.pneumoperitoneum rad then Stage.IIIB
  else if SystemicSigns.stage3_signs sys && IntestinalSigns.stage3_signs int && RadiographicSigns.stage2b_findings rad then Stage.IIIA
  else if SystemicSigns.stage2b_signs sys && IntestinalSigns.stage2_signs int && RadiographicSigns.stage2b_findings rad then Stage.IIB
  else if IntestinalSigns.stage2b_signs int && IntestinalSigns.stage2_signs int && RadiographicSigns.stage2b_findings rad then Stage.IIB
  else if RadiographicSigns.definite_nec_findings rad && IntestinalSigns.stage2_signs int then Stage.IIA
  else if IntestinalSigns.stage1b_signs int && SystemicSigns.stage1_signs sys then Stage.IB
  else Stage.IA.

Definition has_nec_evidence_before_perforation (c : ClinicalState.t) : bool :=
  let rad := ClinicalState.radiographic c in
  let int := ClinicalState.intestinal c in
  RadiographicSigns.pneumatosis_intestinalis rad ||
  RadiographicSigns.portal_venous_gas rad ||
  IntestinalSigns.stage2_signs int ||
  IntestinalSigns.stage3_signs int.

Definition diagnose (c : ClinicalState.t) : Diagnosis.t :=
  let rad := ClinicalState.radiographic c in
  if negb (has_any_findings c) then Diagnosis.NotNEC
  else if RadiographicSigns.pneumoperitoneum rad && negb (has_nec_evidence_before_perforation c)
       then Diagnosis.SuspectedSIP
  else
    let stage := classify_stage c in
    match stage with
    | Stage.IA | Stage.IB => Diagnosis.SuspectedNEC stage
    | _ => Diagnosis.ConfirmedNEC stage
    end.

Definition classify (c : ClinicalState.t) : Stage.t :=
  classify_stage c.

Lemma pneumoperitoneum_forces_IIIB : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify c = Stage.IIIB.
Proof.
  intros c H. unfold classify, classify_stage. rewrite H. reflexivity.
Qed.

Lemma classify_always_valid : forall c,
  1 <= Stage.to_nat (classify c) <= 6.
Proof.
  intros c. split.
  - destruct (classify c); simpl; lia.
  - destruct (classify c); simpl; lia.
Qed.

Lemma no_findings_diagnoses_not_nec : forall c,
  has_any_findings c = false -> diagnose c = Diagnosis.NotNEC.
Proof.
  intros c H. unfold diagnose. rewrite H. reflexivity.
Qed.

End Classification.

Module Treatment.

Inductive t : Type :=
  | NPO_Antibiotics_3days : t
  | NPO_Antibiotics_7to10days : t
  | NPO_Antibiotics_14days : t
  | SurgicalIntervention : t.

Definition of_stage (s : Stage.t) : t :=
  match s with
  | Stage.IA => NPO_Antibiotics_3days
  | Stage.IB => NPO_Antibiotics_3days
  | Stage.IIA => NPO_Antibiotics_7to10days
  | Stage.IIB => NPO_Antibiotics_7to10days
  | Stage.IIIA => NPO_Antibiotics_14days
  | Stage.IIIB => SurgicalIntervention
  end.

Definition npo_duration_days (tx : t) : nat :=
  match tx with
  | NPO_Antibiotics_3days => 3
  | NPO_Antibiotics_7to10days => 10
  | NPO_Antibiotics_14days => 14
  | SurgicalIntervention => 14
  end.

Definition requires_surgery (tx : t) : bool :=
  match tx with
  | SurgicalIntervention => true
  | _ => false
  end.

Lemma stage_IIIB_requires_surgery :
  requires_surgery (of_stage Stage.IIIB) = true.
Proof. reflexivity. Qed.

Lemma suspected_nec_conservative : forall s,
  Stage.to_nat s <= 2 -> requires_surgery (of_stage s) = false.
Proof.
  intros s H. destruct s; simpl in *; try reflexivity; lia.
Qed.

End Treatment.

Module SurgicalIndications.

Inductive Indication : Type :=
  | Pneumoperitoneum : Indication
  | FixedLoop : Indication
  | AbdominalWallErythema : Indication
  | ClinicalDeterioration : Indication
  | PositiveParacentesis : Indication
  | PortalVenousGasWithDeterioration : Indication.

Record SurgicalContext : Type := MkSurgicalContext {
  has_pneumoperitoneum : bool;
  has_fixed_loop : bool;
  has_abdominal_wall_erythema : bool;
  clinical_deterioration_despite_treatment : bool;
  positive_paracentesis : bool;
  portal_venous_gas_with_deterioration : bool
}.

Definition absolute_indication (ctx : SurgicalContext) : bool :=
  has_pneumoperitoneum ctx.

Definition relative_indications_count (ctx : SurgicalContext) : nat :=
  (if has_fixed_loop ctx then 1 else 0) +
  (if has_abdominal_wall_erythema ctx then 1 else 0) +
  (if clinical_deterioration_despite_treatment ctx then 1 else 0) +
  (if positive_paracentesis ctx then 1 else 0) +
  (if portal_venous_gas_with_deterioration ctx then 1 else 0).

Definition surgery_indicated (ctx : SurgicalContext) : bool :=
  absolute_indication ctx || (2 <=? relative_indications_count ctx).

Lemma pneumoperitoneum_absolute : forall ctx,
  has_pneumoperitoneum ctx = true -> surgery_indicated ctx = true.
Proof.
  intros ctx H. unfold surgery_indicated, absolute_indication. rewrite H. reflexivity.
Qed.

End SurgicalIndications.

Module WitnessExamples.

Definition preterm_risk_factors : RiskFactors.t :=
  RiskFactors.MkRiskFactors 26 800 true false false false true false.

Definition abnormal_labs : LabValues.t :=
  LabValues.MkLabValues 3 1000 80 25 8 35 720 10 42 60.

Definition stage_IIA_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true true false true false false false false false false.

Definition stage_IIA_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns false false false false true true false false false false.

Definition stage_IIA_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false true false true false false false.

Definition stage_IIA_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    abnormal_labs
    stage_IIA_witness_systemic
    stage_IIA_witness_intestinal
    stage_IIA_witness_radiographic
    12.

Lemma stage_IIA_witness_classifies_correctly :
  Classification.classify stage_IIA_witness = Stage.IIA.
Proof. reflexivity. Qed.

Lemma stage_IIA_witness_is_high_risk :
  ClinicalState.is_high_risk_patient stage_IIA_witness = true.
Proof. reflexivity. Qed.

Definition stage_IIIB_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false false false true true false true.

Definition stage_IIIB_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    abnormal_labs
    SystemicSigns.none
    IntestinalSigns.none
    stage_IIIB_witness_radiographic
    48.

Lemma stage_IIIB_witness_classifies_correctly :
  Classification.classify stage_IIIB_witness = Stage.IIIB.
Proof. reflexivity. Qed.

Lemma stage_IIIB_witness_requires_surgery :
  Treatment.requires_surgery (Treatment.of_stage (Classification.classify stage_IIIB_witness)) = true.
Proof. reflexivity. Qed.

Definition stage_IA_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true false false true false false false false false false.

Definition stage_IA_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns true true true false false false false false false false.

Definition stage_IA_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    ClinicalState.default_labs
    stage_IA_witness_systemic
    stage_IA_witness_intestinal
    RadiographicSigns.none
    4.

Lemma stage_IA_witness_classifies_correctly :
  Classification.classify stage_IA_witness = Stage.IA.
Proof. reflexivity. Qed.

Definition stage_IB_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true false true false false false false false false false.

Definition stage_IB_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns false false false true false false false false false false.

Definition stage_IB_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    ClinicalState.default_labs
    stage_IB_witness_systemic
    stage_IB_witness_intestinal
    RadiographicSigns.none
    6.

Lemma stage_IB_witness_classifies_correctly :
  Classification.classify stage_IB_witness = Stage.IB.
Proof. reflexivity. Qed.

Definition stage_IIB_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true true false true true true false false false false.

Definition stage_IIB_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns false true false false true true true false false false.

Definition stage_IIB_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false true false false true true false.

Definition stage_IIB_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    abnormal_labs
    stage_IIB_witness_systemic
    stage_IIB_witness_intestinal
    stage_IIB_witness_radiographic
    24.

Lemma stage_IIB_witness_classifies_correctly :
  Classification.classify stage_IIB_witness = Stage.IIB.
Proof. reflexivity. Qed.

Definition stage_IIIA_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true true true true true true true true false false.

Definition stage_IIIA_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns false true false false true true false false true true.

Definition stage_IIIA_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false true false true true true false.

Definition stage_IIIA_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    preterm_risk_factors
    abnormal_labs
    stage_IIIA_witness_systemic
    stage_IIIA_witness_intestinal
    stage_IIIA_witness_radiographic
    36.

Lemma stage_IIIA_witness_classifies_correctly :
  Classification.classify stage_IIIA_witness = Stage.IIIA.
Proof. reflexivity. Qed.

End WitnessExamples.

Module CounterexampleAttempts.

Definition no_findings : ClinicalState.t :=
  ClinicalState.empty.

Lemma no_findings_cannot_be_IIIB :
  Classification.classify no_findings <> Stage.IIIB.
Proof. discriminate. Qed.

Lemma no_findings_cannot_require_surgery :
  Treatment.requires_surgery (Treatment.of_stage (Classification.classify no_findings)) = false.
Proof. reflexivity. Qed.

Definition systemic_only : ClinicalState.t :=
  ClinicalState.MkClinicalState
    ClinicalState.default_risk_factors
    ClinicalState.default_labs
    (SystemicSigns.MkSystemicSigns true true true true true true true true true true)
    IntestinalSigns.none
    RadiographicSigns.none
    24.

Lemma systemic_signs_alone_insufficient_for_definite_nec :
  Stage.to_nat (Classification.classify systemic_only) < Stage.to_nat Stage.IIA.
Proof. simpl. lia. Qed.

Definition term_infant_low_risk : ClinicalState.t :=
  ClinicalState.MkClinicalState
    (RiskFactors.MkRiskFactors 40 3500 false false false false false false)
    ClinicalState.default_labs
    SystemicSigns.none
    IntestinalSigns.none
    RadiographicSigns.none
    0.

Lemma term_infant_not_high_risk :
  ClinicalState.is_high_risk_patient term_infant_low_risk = false.
Proof. reflexivity. Qed.

End CounterexampleAttempts.

Module SafetyProperties.

Theorem every_patient_staged : forall c,
  exists s, Classification.classify c = s.
Proof. intros c. exists (Classification.classify c). reflexivity. Qed.

Theorem perforation_always_surgical : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  Treatment.requires_surgery (Treatment.of_stage (Classification.classify c)) = true.
Proof.
  intros c H.
  rewrite (Classification.pneumoperitoneum_forces_IIIB c H).
  reflexivity.
Qed.

Theorem stage_determines_treatment : forall c1 c2,
  Classification.classify c1 = Classification.classify c2 ->
  Treatment.of_stage (Classification.classify c1) = Treatment.of_stage (Classification.classify c2).
Proof.
  intros c1 c2 H. rewrite H. reflexivity.
Qed.

Theorem npo_duration_at_least_3 : forall s,
  3 <= Treatment.npo_duration_days (Treatment.of_stage s).
Proof.
  intros []; simpl; lia.
Qed.

Theorem surgery_only_at_IIIB : forall s,
  Treatment.requires_surgery (Treatment.of_stage s) = true -> s = Stage.IIIB.
Proof.
  intros s H. destruct s; simpl in H; try discriminate. reflexivity.
Qed.

End SafetyProperties.

Module StageProgression.

Definition is_suspected (s : Stage.t) : bool :=
  match s with
  | Stage.IA | Stage.IB => true
  | _ => false
  end.

Definition is_definite (s : Stage.t) : bool :=
  match s with
  | Stage.IIA | Stage.IIB => true
  | _ => false
  end.

Definition is_advanced (s : Stage.t) : bool :=
  match s with
  | Stage.IIIA | Stage.IIIB => true
  | _ => false
  end.

Definition category (s : Stage.t) : nat :=
  match s with
  | Stage.IA | Stage.IB => 1
  | Stage.IIA | Stage.IIB => 2
  | Stage.IIIA | Stage.IIIB => 3
  end.

Lemma suspected_category_1 : forall s,
  is_suspected s = true -> category s = 1.
Proof. intros []; simpl; intro H; try discriminate; reflexivity. Qed.

Lemma definite_category_2 : forall s,
  is_definite s = true -> category s = 2.
Proof. intros []; simpl; intro H; try discriminate; reflexivity. Qed.

Lemma advanced_category_3 : forall s,
  is_advanced s = true -> category s = 3.
Proof. intros []; simpl; intro H; try discriminate; reflexivity. Qed.

Lemma stage_nat_determines_category : forall s,
  category s = (Stage.to_nat s + 1) / 2.
Proof. intros []; reflexivity. Qed.

End StageProgression.

Module Prognosis.

Inductive Outcome : Type :=
  | FullRecovery : Outcome
  | Stricture : Outcome
  | ShortBowelSyndrome : Outcome
  | Recurrence : Outcome
  | Death : Outcome.

Definition mortality_risk_percent (s : Stage.t) : nat :=
  match s with
  | Stage.IA => 0
  | Stage.IB => 0
  | Stage.IIA => 5
  | Stage.IIB => 10
  | Stage.IIIA => 20
  | Stage.IIIB => 30
  end.

Definition stricture_risk_percent (s : Stage.t) : nat :=
  match s with
  | Stage.IA => 0
  | Stage.IB => 0
  | Stage.IIA => 10
  | Stage.IIB => 20
  | Stage.IIIA => 25
  | Stage.IIIB => 35
  end.

Definition short_bowel_risk_percent (s : Stage.t) : nat :=
  match s with
  | Stage.IA => 0
  | Stage.IB => 0
  | Stage.IIA => 0
  | Stage.IIB => 5
  | Stage.IIIA => 10
  | Stage.IIIB => 25
  end.

Definition requires_long_term_followup (s : Stage.t) : bool :=
  match s with
  | Stage.IA | Stage.IB => false
  | _ => true
  end.

Definition neurodevelopmental_risk_elevated (s : Stage.t) (required_surgery : bool) : bool :=
  match s with
  | Stage.IIIA | Stage.IIIB => true
  | Stage.IIA | Stage.IIB => required_surgery
  | _ => false
  end.

Lemma stage_IIIB_highest_mortality :
  forall s, mortality_risk_percent s <= mortality_risk_percent Stage.IIIB.
Proof. intros []; simpl; lia. Qed.

Lemma suspected_nec_no_mortality :
  forall s, StageProgression.is_suspected s = true -> mortality_risk_percent s = 0.
Proof. intros []; simpl; intro H; try discriminate; reflexivity. Qed.

Lemma definite_nec_requires_followup :
  forall s, StageProgression.is_definite s = true -> requires_long_term_followup s = true.
Proof. intros []; simpl; intro H; try discriminate; reflexivity. Qed.

End Prognosis.

Module BellCriteria.

Record StageCriteria : Type := MkCriteria {
  crit_stage : Stage.t;
  crit_requires_systemic : bool;
  crit_systemic_level : nat;
  crit_requires_intestinal : bool;
  crit_intestinal_level : nat;
  crit_requires_radiographic : bool;
  crit_radiographic_level : nat
}.

Definition stage_IA_criteria :=
  MkCriteria Stage.IA true 1 true 1 false 0.

Definition stage_IB_criteria :=
  MkCriteria Stage.IB true 1 true 1 false 0.

Definition stage_IIA_criteria :=
  MkCriteria Stage.IIA true 1 true 2 true 2.

Definition stage_IIB_criteria :=
  MkCriteria Stage.IIB true 2 true 2 true 2.

Definition stage_IIIA_criteria :=
  MkCriteria Stage.IIIA true 3 true 3 true 2.

Definition stage_IIIB_criteria :=
  MkCriteria Stage.IIIB true 3 true 3 true 3.

Definition compute_systemic_level (s : SystemicSigns.t) : nat :=
  if SystemicSigns.stage3_signs s then 3
  else if SystemicSigns.stage2b_signs s then 2
  else if SystemicSigns.stage1_signs s then 1
  else 0.

Definition compute_intestinal_level (i : IntestinalSigns.t) : nat :=
  if IntestinalSigns.stage3_signs i then 3
  else if IntestinalSigns.stage2b_signs i || IntestinalSigns.stage2_signs i then 2
  else if IntestinalSigns.stage1b_signs i then 1
  else if IntestinalSigns.stage1a_signs i then 1
  else 0.

Definition compute_radiographic_level (r : RadiographicSigns.t) : nat :=
  if RadiographicSigns.pneumoperitoneum r then 3
  else if RadiographicSigns.stage2b_findings r then 2
  else if RadiographicSigns.definite_nec_findings r then 2
  else if RadiographicSigns.stage2a_findings r then 2
  else if RadiographicSigns.stage1_findings r then 1
  else 0.

Definition meets_criteria (c : ClinicalState.t) (crit : StageCriteria) : bool :=
  let sys_lv := compute_systemic_level (ClinicalState.systemic c) in
  let int_lv := compute_intestinal_level (ClinicalState.intestinal c) in
  let rad_lv := compute_radiographic_level (ClinicalState.radiographic c) in
  (negb (crit_requires_systemic crit) || (crit_systemic_level crit <=? sys_lv)) &&
  (negb (crit_requires_intestinal crit) || (crit_intestinal_level crit <=? int_lv)) &&
  (negb (crit_requires_radiographic crit) || (crit_radiographic_level crit <=? rad_lv)).

Definition classify_declarative (c : ClinicalState.t) : Stage.t :=
  if meets_criteria c stage_IIIB_criteria then Stage.IIIB
  else if meets_criteria c stage_IIIA_criteria then Stage.IIIA
  else if meets_criteria c stage_IIB_criteria then Stage.IIB
  else if meets_criteria c stage_IIA_criteria then Stage.IIA
  else if meets_criteria c stage_IB_criteria then Stage.IB
  else Stage.IA.

End BellCriteria.
