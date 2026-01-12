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

Lemma severity_score_max : forall s, severity_score s <= 22.
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
  pneumatosis_intestinalis r || portal_venous_gas r.

Definition perforation_finding (r : t) : bool :=
  pneumoperitoneum r.

Lemma pneumoperitoneum_implies_stage3b : forall r,
  pneumoperitoneum r = true -> stage3b_findings r = true.
Proof. intros r H. unfold stage3b_findings. exact H. Qed.

End RadiographicSigns.

Module ClinicalState.

Record t : Type := MkClinicalState {
  systemic : SystemicSigns.t;
  intestinal : IntestinalSigns.t;
  radiographic : RadiographicSigns.t
}.

Definition empty : t :=
  MkClinicalState SystemicSigns.none IntestinalSigns.none RadiographicSigns.none.

End ClinicalState.

Module Classification.

Definition classify (c : ClinicalState.t) : Stage.t :=
  let sys := ClinicalState.systemic c in
  let int := ClinicalState.intestinal c in
  let rad := ClinicalState.radiographic c in
  if RadiographicSigns.pneumoperitoneum rad then Stage.IIIB
  else if SystemicSigns.stage3_signs sys && IntestinalSigns.stage3_signs int then Stage.IIIA
  else if SystemicSigns.stage2b_signs sys && RadiographicSigns.stage2b_findings rad then Stage.IIB
  else if IntestinalSigns.stage2b_signs int && RadiographicSigns.stage2b_findings rad then Stage.IIB
  else if RadiographicSigns.definite_nec_findings rad && IntestinalSigns.stage2_signs int then Stage.IIA
  else if IntestinalSigns.stage1b_signs int && SystemicSigns.stage1_signs sys then Stage.IB
  else if IntestinalSigns.stage1a_signs int && SystemicSigns.stage1_signs sys then Stage.IA
  else Stage.IA.

Lemma pneumoperitoneum_forces_IIIB : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify c = Stage.IIIB.
Proof.
  intros c H. unfold classify. rewrite H. reflexivity.
Qed.

Lemma classify_always_valid : forall c,
  1 <= Stage.to_nat (classify c) <= 6.
Proof.
  intros c. split.
  - destruct (classify c); simpl; lia.
  - destruct (classify c); simpl; lia.
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

Definition stage_IIA_witness_systemic : SystemicSigns.t :=
  SystemicSigns.MkSystemicSigns true true false true false false false false false false.

Definition stage_IIA_witness_intestinal : IntestinalSigns.t :=
  IntestinalSigns.MkIntestinalSigns false false false false true true false false false false.

Definition stage_IIA_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false true false true false false false.

Definition stage_IIA_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    stage_IIA_witness_systemic
    stage_IIA_witness_intestinal
    stage_IIA_witness_radiographic.

Lemma stage_IIA_witness_classifies_correctly :
  Classification.classify stage_IIA_witness = Stage.IIA.
Proof. reflexivity. Qed.

Definition stage_IIIB_witness_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false false false true true false true.

Definition stage_IIIB_witness : ClinicalState.t :=
  ClinicalState.MkClinicalState
    SystemicSigns.none
    IntestinalSigns.none
    stage_IIIB_witness_radiographic.

Lemma stage_IIIB_witness_classifies_correctly :
  Classification.classify stage_IIIB_witness = Stage.IIIB.
Proof. reflexivity. Qed.

Lemma stage_IIIB_witness_requires_surgery :
  Treatment.requires_surgery (Treatment.of_stage (Classification.classify stage_IIIB_witness)) = true.
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
    (SystemicSigns.MkSystemicSigns true true true true true true true true true true)
    IntestinalSigns.none
    RadiographicSigns.none.

Lemma systemic_signs_alone_insufficient_for_definite_nec :
  Stage.to_nat (Classification.classify systemic_only) < Stage.to_nat Stage.IIA.
Proof. simpl. lia. Qed.

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
