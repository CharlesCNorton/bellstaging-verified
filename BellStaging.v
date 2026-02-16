(******************************************************************************)
(*                                                                            *)
(*                  Bell Staging for Necrotizing Enterocolitis                *)
(*                                                                            *)
(*     Formalization of modified Bell staging criteria for NEC in neonates:   *)
(*     Stage I (suspected), Stage II (definite), Stage III (advanced).        *)
(*     Clinical signs, radiographic findings, and systemic manifestations.    *)
(*     Decision predicates for staging and surgical intervention triggers.    *)
(*                                                                            *)
(*     'I will stand at my watch and station myself on the ramparts;          *)
(*      I will look to see what he will say to me, and what answer            *)
(*      I am to give to this complaint.' - Habakkuk 2:1                       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 6, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*                              CURE LIST                                     *)
(*                                                                            *)
(*  Sequenced so each item depends only on earlier ones.                     *)
(*                                                                            *)
(*  1. [DONE] Consolidate classify_stage IIB into single canonical form.     *)
(*  2. [DONE] Align IIIA radiographic axis between both classifiers.         *)
(*  3. [DONE] Deleted classify_canonical alias.                              *)
(*  4. [DONE] Deleted Diagnosis.requires_surgery (dead code);                *)
(*     Treatment.requires_surgery and SurgicalIndications.surgery_indicated  *)
(*     are the two canonical predicates.                                     *)
(*  5. [DONE] Wire VitalSigns.hypotension into classify_stage via            *)
(*     effective_hypotension (MAP < GA weeks when vitals available).          *)
(*  6. [DONE] Route ClinicalState.has_dic into effective_stage3_sys.          *)
(*  7. [DONE] Wire lab-derived acidosis, thrombocytopenia, neutropenia       *)
(*     into classify_stage via effective_stage2b_sys/effective_stage3_sys.   *)
(*  8. [DONE] most_likely_diagnosis now uses confidence score comparison.    *)
(*  9. [DONE] SIP now excludes on radiographic NEC (pneumatosis/PVG),       *)
(*     not mild feeding intolerance.                                         *)
(* 10. [DONE] add_observation returns option, rejects out-of-order.          *)
(* 11. [DONE] compute_trajectory uses max_stage to detect non-monotonic      *)
(*     paths; peak > current triggers different logic.                       *)
(* 12. [DONE] Both modules now use velocity >20 for RapidDeterioration.      *)
(* 13. [DONE] hours_to_reassess takes stage_nat; Stage III halves interval.  *)
(* 14. Add sign_timestamp or sign_active fields, filter stale signs.         *)
(* 15. Prove forall c, classify_stage c = classify_declarative c.            *)
(* 16. Prove signs_subset c1 c2 -> Stage.leb (classify c1) (classify c2).   *)
(* 17. Prove pneumoperitoneum c = false -> ... -> classify c <> Stage.IIIB.  *)
(* 18. Prove totality via boolean reflection or enumeration;                 *)
(*     current classify_total is tautological.                               *)
(* 19. Prove each stage has witness and witnesses span all stages.           *)
(* 20. Define valid_transition as inductive relation with eauto hints.       *)
(* 21. Add Stabilization -> SurgicalEvaluation to valid transitions.         *)
(* 22. Replace prognosis nat with record { low; mid; high }.                 *)
(* 23. Add module with published case studies as witness validation suite.   *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

(* Risk score weights with provenance *)
Definition lucas_cole_1990 : nat := 6.
Definition sharma_2006 : nat := 7.
Definition mcelhinney_2000 : nat := 8.

Definition weight_extremely_preterm := MkParam 4 neu_walker_2011 2011.
Definition weight_very_preterm := MkParam 3 neu_walker_2011 2011.
Definition weight_moderate_preterm := MkParam 2 neu_walker_2011 2011.
Definition weight_elbw := MkParam 4 gephart_2012 2012.
Definition weight_vlbw := MkParam 3 gephart_2012 2012.
Definition weight_lbw := MkParam 1 gephart_2012 2012.
Definition weight_formula_fed := MkParam 1 lucas_cole_1990 1990.
Definition weight_breast_milk_protective := MkParam 2 lucas_cole_1990 1990.
Definition weight_perinatal_asphyxia := MkParam 2 sharma_2006 2006.
Definition weight_chd := MkParam 2 mcelhinney_2000 2000.
Definition weight_polycythemia := MkParam 1 walsh_kliegman_1986 1986.
Definition weight_umbilical_catheter := MkParam 1 walsh_kliegman_1986 1986.
Definition weight_exchange_transfusion := MkParam 1 walsh_kliegman_1986 1986.

(* Organ failure thresholds - nSOFA/SNAP-II based *)
Definition wynn_2017 : nat := 9.
Definition richardson_2001 : nat := 10.

Definition pf_ratio_severe := MkParam 100 wynn_2017 2017.
Definition pf_ratio_moderate := MkParam 200 wynn_2017 2017.
Definition pf_ratio_mild := MkParam 300 wynn_2017 2017.
Definition fio2_mild := MkParam 30 richardson_2001 2001.
Definition fio2_moderate := MkParam 40 richardson_2001 2001.
Definition map_hypotension := MkParam 30 wynn_2017 2017.
Definition lactate_elevated_x10 := MkParam 20 wynn_2017 2017.
Definition bilirubin_mild := MkParam 2 wynn_2017 2017.
Definition bilirubin_moderate := MkParam 6 wynn_2017 2017.
Definition bilirubin_severe := MkParam 12 wynn_2017 2017.
Definition platelets_moderate := MkParam 100 wynn_2017 2017.
Definition platelets_severe := MkParam 50 wynn_2017 2017.
Definition inr_elevated_x100 := MkParam 150 wynn_2017 2017.
Definition inr_severe_x100 := MkParam 200 wynn_2017 2017.
Definition creatinine_mild_x10 := MkParam 10 wynn_2017 2017.
Definition creatinine_moderate_x10 := MkParam 15 wynn_2017 2017.
Definition creatinine_severe_x10 := MkParam 20 wynn_2017 2017.
Definition urine_oliguria_x10 := MkParam 5 richardson_2001 2001.
Definition urine_low_x10 := MkParam 10 richardson_2001 2001.
Definition organ_failure_threshold := MkParam 2 wynn_2017 2017.

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

(* Thresholds from ClinicalParameters with provenance tracking *)
Definition extremely_preterm_weeks : nat :=
  ClinicalParameters.param_value ClinicalParameters.extremely_preterm_threshold.
Definition elbw_grams : nat :=
  ClinicalParameters.param_value ClinicalParameters.elbw_threshold.
Definition vlbw_grams : nat :=
  ClinicalParameters.param_value ClinicalParameters.vlbw_threshold.

Definition extremely_preterm (r : t) : bool :=
  gestational_age_weeks r <? extremely_preterm_weeks.

Definition very_preterm (r : t) : bool :=
  (extremely_preterm_weeks <=? gestational_age_weeks r) && (gestational_age_weeks r <? 32).

Definition moderate_preterm (r : t) : bool :=
  (32 <=? gestational_age_weeks r) && (gestational_age_weeks r <? 37).

Definition term (r : t) : bool :=
  37 <=? gestational_age_weeks r.

Definition extremely_low_birth_weight (r : t) : bool :=
  birth_weight_grams r <? elbw_grams.

Definition very_low_birth_weight (r : t) : bool :=
  (elbw_grams <=? birth_weight_grams r) && (birth_weight_grams r <? vlbw_grams).

Definition low_birth_weight (r : t) : bool :=
  (vlbw_grams <=? birth_weight_grams r) && (birth_weight_grams r <? 2500).

(* Risk score weights now in ClinicalParameters with provenance *)
Definition w_extremely_preterm : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_extremely_preterm.
Definition w_very_preterm : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_very_preterm.
Definition w_moderate_preterm : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_moderate_preterm.
Definition w_elbw : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_elbw.
Definition w_vlbw : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_vlbw.
Definition w_lbw : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_lbw.
Definition w_formula_fed : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_formula_fed.
Definition w_breast_milk_protective : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_breast_milk_protective.
Definition w_perinatal_asphyxia : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_perinatal_asphyxia.
Definition w_chd : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_chd.
Definition w_polycythemia : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_polycythemia.
Definition w_umbilical_catheter : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_umbilical_catheter.
Definition w_exchange_transfusion : nat :=
  ClinicalParameters.param_value ClinicalParameters.weight_exchange_transfusion.

Definition risk_score_raw (r : t) : nat :=
  (if extremely_preterm r then w_extremely_preterm
   else if very_preterm r then w_very_preterm
   else if moderate_preterm r then w_moderate_preterm
   else 0) +
  (if extremely_low_birth_weight r then w_elbw
   else if very_low_birth_weight r then w_vlbw
   else if low_birth_weight r then w_lbw
   else 0) +
  (if formula_fed r then w_formula_fed else 0) +
  (if history_of_perinatal_asphyxia r then w_perinatal_asphyxia else 0) +
  (if congenital_heart_disease r then w_chd else 0) +
  (if polycythemia r then w_polycythemia else 0) +
  (if umbilical_catheter r then w_umbilical_catheter else 0) +
  (if exchange_transfusion r then w_exchange_transfusion else 0).

Definition protective_factor (r : t) : nat :=
  if formula_fed r then 0 else w_breast_milk_protective.

Definition risk_score (r : t) : nat :=
  risk_score_raw r - protective_factor r.

Definition high_risk (r : t) : bool :=
  6 <=? risk_score r.

Lemma extremely_preterm_high_risk : forall r,
  extremely_preterm r = true ->
  extremely_low_birth_weight r = true ->
  high_risk r = true.
Proof.
  intros r Hp Hw. unfold high_risk, risk_score, risk_score_raw, protective_factor.
  rewrite Hp, Hw. simpl.
  destruct (formula_fed r); reflexivity.
Qed.

End RiskFactors.

Module LabValues.

(* Fixed-point encoding conventions:
   - procalcitonin_ng_mL_x10: actual ng/mL * 10 (e.g., 0.5 ng/mL = 5)
   - lactate_mmol_L_x10: actual mmol/L * 10 (e.g., 2.0 mmol/L = 20)
   - ph_x100: actual pH * 100 (e.g., 7.35 = 735)
   This avoids floating-point while preserving clinically relevant precision.
   All thresholds in predicates below use the same scaling. *)

Record t : Type := MkLabValues {
  wbc_k_per_uL : nat;                (* thousands per microliter *)
  absolute_neutrophil_count : nat;   (* cells per microliter *)
  platelet_k_per_uL : nat;           (* thousands per microliter *)
  crp_mg_L : nat;                    (* mg/L, integer sufficient *)
  procalcitonin_ng_mL_x10 : nat;     (* ng/mL * 10 *)
  lactate_mmol_L_x10 : nat;          (* mmol/L * 10 *)
  ph_x100 : nat;                     (* pH * 100 *)
  base_deficit : nat;                (* mEq/L, always positive in acidosis *)
  pco2_mmHg : nat;                   (* mmHg, integer sufficient *)
  glucose_mg_dL : nat                (* mg/dL, integer sufficient *)
}.

Definition leukopenia (l : t) : bool :=
  wbc_k_per_uL l <? 5.

Definition leukocytosis (l : t) : bool :=
  25 <? wbc_k_per_uL l.

Definition neutropenia (l : t) : bool :=
  absolute_neutrophil_count l <? 1500.

(* Thresholds from ClinicalParameters *)
Definition thrombocytopenia_threshold : nat :=
  ClinicalParameters.param_value ClinicalParameters.thrombocytopenia_threshold.
Definition severe_thrombocytopenia_threshold : nat :=
  ClinicalParameters.param_value ClinicalParameters.severe_thrombocytopenia_threshold.

Definition thrombocytopenia (l : t) : bool :=
  platelet_k_per_uL l <? thrombocytopenia_threshold.

Definition severe_thrombocytopenia (l : t) : bool :=
  platelet_k_per_uL l <? severe_thrombocytopenia_threshold.

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
  (if severe_thrombocytopenia l then 2
   else if thrombocytopenia l then 1
   else 0) +
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

Module CoagulationPanel.

(* Fixed-point encoding conventions:
   - pt_seconds_x10: actual seconds * 10 (e.g., 15.0 sec = 150)
   - inr_x100: actual INR * 100 (e.g., 1.5 = 150)
   - ionized_calcium_x100: actual mmol/L * 100 (e.g., 1.0 mmol/L = 100)
   Normal ranges: PT 11-15 sec (110-150), INR 0.9-1.1 (90-110), iCa 1.1-1.3 (110-130) *)

Record t : Type := MkCoagPanel {
  pt_seconds_x10 : nat;       (* seconds * 10 *)
  inr_x100 : nat;             (* INR * 100 *)
  fibrinogen_mg_dL : nat;     (* mg/dL, integer sufficient *)
  ionized_calcium_x100 : nat  (* mmol/L * 100 *)
}.

(* Using same INR thresholds as NeonatalOrganFailure for consistency *)
Definition inr_threshold : nat :=
  ClinicalParameters.param_value ClinicalParameters.inr_elevated_x100.

Definition pt_prolonged (c : t) : bool :=
  150 <? pt_seconds_x10 c.

Definition inr_elevated (c : t) : bool :=
  inr_threshold <? inr_x100 c.

Definition hypofibrinogenemia (c : t) : bool :=
  fibrinogen_mg_dL c <? 100.

Definition hypocalcemia (c : t) : bool :=
  ionized_calcium_x100 c <? 100.

Definition coagulopathy_present (c : t) : bool :=
  pt_prolonged c || inr_elevated c || hypofibrinogenemia c.

Definition dic_criteria_met (c : t) (platelets_low : bool) (elevated_lactate : bool) : bool :=
  platelets_low && coagulopathy_present c && elevated_lactate.

Definition calcium_replacement_needed (c : t) (prbc_units : nat) : bool :=
  hypocalcemia c || (4 <=? prbc_units).

Lemma coagulopathy_implies_one_abnormal : forall c,
  coagulopathy_present c = true ->
  pt_prolonged c = true \/ inr_elevated c = true \/ hypofibrinogenemia c = true.
Proof.
  intros c H. unfold coagulopathy_present in H.
  apply orb_true_iff in H. destruct H as [H | H].
  - apply orb_true_iff in H. destruct H as [H | H].
    + left. exact H.
    + right. left. exact H.
  - right. right. exact H.
Qed.

End CoagulationPanel.

Module Microbiology.

(* Blood culture status for sepsis evaluation *)
Inductive CultureStatus : Type :=
  | NotCollected : CultureStatus
  | Pending : CultureStatus
  | Negative : CultureStatus
  | PositiveGramNeg : CultureStatus    (* E. coli, Klebsiella, etc. - common in NEC *)
  | PositiveGramPos : CultureStatus    (* Staph, Strep - less specific *)
  | PositiveFungal : CultureStatus.    (* Candida - poor prognosis *)

Record t : Type := MkMicrobiology {
  blood_culture : CultureStatus;
  blood_culture_collected_h : option nat;  (* hours since symptom onset *)
  blood_culture_resulted_h : option nat;
  csf_culture : CultureStatus;             (* for meningitis rule-out *)
  csf_culture_collected_h : option nat;
  csf_culture_resulted_h : option nat;
  peritoneal_culture : CultureStatus;      (* if paracentesis done *)
  peritoneal_culture_collected_h : option nat;
  peritoneal_culture_resulted_h : option nat
}.

Definition none : t :=
  MkMicrobiology NotCollected None None NotCollected None None NotCollected None None.

Definition is_positive (c : CultureStatus) : bool :=
  match c with
  | PositiveGramNeg | PositiveGramPos | PositiveFungal => true
  | _ => false
  end.

Definition blood_culture_positive (m : t) : bool :=
  is_positive (blood_culture m).

Definition any_culture_positive (m : t) : bool :=
  is_positive (blood_culture m) ||
  is_positive (csf_culture m) ||
  is_positive (peritoneal_culture m).

Definition gram_negative_sepsis (m : t) : bool :=
  match blood_culture m with
  | PositiveGramNeg => true
  | _ => false
  end.

Definition fungal_sepsis (m : t) : bool :=
  match blood_culture m with
  | PositiveFungal => true
  | _ => false
  end.

Lemma positive_implies_any_positive : forall m,
  blood_culture_positive m = true -> any_culture_positive m = true.
Proof.
  intros m H. unfold any_culture_positive, blood_culture_positive in *.
  rewrite H. reflexivity.
Qed.

End Microbiology.

Module VitalSigns.

(* Neonatal vital sign thresholds vary by gestational age and postnatal age.
   Values here are simplified for term/near-term neonates.
   References:
   - Dionne et al. 2012, Pediatr Nephrol 27(9):1647-1657 (BP)
   - Fleming et al. 2011, Lancet 377(9770):1011-1018 (HR, RR)

   Fixed-point encoding:
   - temperature_x10: Celsius * 10 (e.g., 36.5°C = 365)
   - map_mmHg: mean arterial pressure in mmHg (integer sufficient)
   - spo2_percent: oxygen saturation as integer percentage *)

Record t : Type := MkVitalSigns {
  heart_rate_bpm : nat;
  respiratory_rate_bpm : nat;
  temperature_x10 : nat;       (* Celsius * 10 *)
  systolic_bp_mmHg : nat;
  diastolic_bp_mmHg : nat;
  map_mmHg : nat;              (* mean arterial pressure *)
  spo2_percent : nat
}.

Definition normal : t :=
  MkVitalSigns 140 40 370 65 40 48 98.

(* Abnormality thresholds *)
Definition tachycardia (v : t) : bool :=
  180 <? heart_rate_bpm v.

Definition bradycardia (v : t) : bool :=
  heart_rate_bpm v <? 100.

Definition tachypnea (v : t) : bool :=
  60 <? respiratory_rate_bpm v.

Definition hypothermia (v : t) : bool :=
  temperature_x10 v <? 365.

Definition hyperthermia (v : t) : bool :=
  380 <? temperature_x10 v.

Definition temperature_instability (v : t) : bool :=
  hypothermia v || hyperthermia v.

(* Hypotension threshold: MAP < gestational age in weeks is classic rule
   For simplicity, using fixed threshold; clinical use should adjust *)
Definition hypotension (v : t) (gestational_age_weeks : nat) : bool :=
  map_mmHg v <? gestational_age_weeks.

Definition hypotension_fixed (v : t) : bool :=
  map_mmHg v <? 30.

Definition hypoxemia (v : t) : bool :=
  spo2_percent v <? 90.

Definition severe_hypoxemia (v : t) : bool :=
  spo2_percent v <? 85.

(* Shock index (HR/SBP) - elevated suggests poor perfusion *)
Definition shock_index_elevated (v : t) : bool :=
  (systolic_bp_mmHg v * 15) <? (heart_rate_bpm v * 10).

(* Vital sign severity score *)
Definition severity_score (v : t) : nat :=
  (if bradycardia v then 2 else 0) +
  (if tachycardia v then 1 else 0) +
  (if tachypnea v then 1 else 0) +
  (if temperature_instability v then 1 else 0) +
  (if hypotension_fixed v then 3 else 0) +
  (if hypoxemia v then 2 else 0) +
  (if severe_hypoxemia v then 2 else 0).

Lemma bradycardia_tachycardia_exclusive : forall v,
  bradycardia v = true -> tachycardia v = false.
Proof.
  intros v H. unfold bradycardia, tachycardia in *.
  apply Nat.ltb_lt in H.
  apply Nat.ltb_ge. lia.
Qed.

End VitalSigns.

Module NeonatalOrganFailure.

(* Neonatal organ dysfunction scoring based on:
   - nSOFA: Wynn et al. 2017, Pediatr Crit Care Med 18(9):S32-S40
   - SNAP-II: Richardson et al. 2001, Pediatrics 107(1):61-66

   Each organ system scored 0-4 based on severity of dysfunction.
   Total score correlates with mortality risk in sepsis/NEC.
   Thresholds now in ClinicalParameters with provenance. *)

(* Threshold accessors *)
Definition pf_severe : nat := ClinicalParameters.param_value ClinicalParameters.pf_ratio_severe.
Definition pf_moderate : nat := ClinicalParameters.param_value ClinicalParameters.pf_ratio_moderate.
Definition pf_mild : nat := ClinicalParameters.param_value ClinicalParameters.pf_ratio_mild.
Definition fio2_th_mild : nat := ClinicalParameters.param_value ClinicalParameters.fio2_mild.
Definition fio2_th_moderate : nat := ClinicalParameters.param_value ClinicalParameters.fio2_moderate.
Definition map_th : nat := ClinicalParameters.param_value ClinicalParameters.map_hypotension.
Definition lactate_th : nat := ClinicalParameters.param_value ClinicalParameters.lactate_elevated_x10.
Definition bili_mild : nat := ClinicalParameters.param_value ClinicalParameters.bilirubin_mild.
Definition bili_moderate : nat := ClinicalParameters.param_value ClinicalParameters.bilirubin_moderate.
Definition bili_severe : nat := ClinicalParameters.param_value ClinicalParameters.bilirubin_severe.
Definition plt_moderate : nat := ClinicalParameters.param_value ClinicalParameters.platelets_moderate.
Definition plt_severe : nat := ClinicalParameters.param_value ClinicalParameters.platelets_severe.
Definition inr_elevated : nat := ClinicalParameters.param_value ClinicalParameters.inr_elevated_x100.
Definition inr_severe : nat := ClinicalParameters.param_value ClinicalParameters.inr_severe_x100.
Definition cr_mild : nat := ClinicalParameters.param_value ClinicalParameters.creatinine_mild_x10.
Definition cr_moderate : nat := ClinicalParameters.param_value ClinicalParameters.creatinine_moderate_x10.
Definition cr_severe : nat := ClinicalParameters.param_value ClinicalParameters.creatinine_severe_x10.
Definition urine_oliguria : nat := ClinicalParameters.param_value ClinicalParameters.urine_oliguria_x10.
Definition urine_low : nat := ClinicalParameters.param_value ClinicalParameters.urine_low_x10.
Definition organ_fail_th : nat := ClinicalParameters.param_value ClinicalParameters.organ_failure_threshold.

(* Respiratory failure scoring *)
Definition respiratory_score (fio2_percent : nat) (on_ventilator : bool)
    (pao2_fio2_ratio : nat) : nat :=
  if on_ventilator then
    if pao2_fio2_ratio <? pf_severe then 4
    else if pao2_fio2_ratio <? pf_moderate then 3
    else if pao2_fio2_ratio <? pf_mild then 2
    else 1
  else
    if fio2_percent <? fio2_th_mild then 0
    else if fio2_percent <? fio2_th_moderate then 1
    else 2.

(* Cardiovascular failure scoring *)
Definition cardiovascular_score (map_mmHg : nat) (on_vasopressors : bool)
    (lactate_x10 : nat) : nat :=
  if on_vasopressors then
    if lactate_x10 <? lactate_th then 3 else 4
  else if map_mmHg <? map_th then 2
  else if lactate_x10 <? lactate_th then 0 else 1.

(* Hepatic failure scoring *)
Definition hepatic_score (bilirubin_mg_dL : nat) : nat :=
  if bilirubin_mg_dL <? bili_mild then 0
  else if bilirubin_mg_dL <? bili_moderate then 1
  else if bilirubin_mg_dL <? bili_severe then 2
  else 3.

(* Coagulation failure scoring *)
Definition coagulation_score (platelets_k : nat) (inr_x100 : nat) : nat :=
  (if platelets_k <? plt_severe then 2
   else if platelets_k <? plt_moderate then 1
   else 0) +
  (if inr_x100 <? inr_elevated then 0
   else if inr_x100 <? inr_severe then 1
   else 2).

(* Renal failure scoring *)
Definition renal_score (creatinine_mg_dL_x10 : nat) (urine_output_ml_kg_hr_x10 : nat) : nat :=
  (if creatinine_mg_dL_x10 <? cr_mild then 0
   else if creatinine_mg_dL_x10 <? cr_moderate then 1
   else if creatinine_mg_dL_x10 <? cr_severe then 2
   else 3) +
  (if urine_output_ml_kg_hr_x10 <? urine_oliguria then 2
   else if urine_output_ml_kg_hr_x10 <? urine_low then 1
   else 0).

(* Neurologic assessment - simplified for neonates *)
Inductive NeuroStatus : Type :=
  | Normal : NeuroStatus
  | Lethargic : NeuroStatus
  | Obtunded : NeuroStatus
  | Unresponsive : NeuroStatus.

Definition neurologic_score (status : NeuroStatus) : nat :=
  match status with
  | Normal => 0
  | Lethargic => 1
  | Obtunded => 2
  | Unresponsive => 4
  end.

(* Combined organ failure record *)
Record OrganFailureAssessment : Type := MkOrganFailure {
  resp_score : nat;
  cv_score : nat;
  hep_score : nat;
  coag_score : nat;
  renal_score_val : nat;
  neuro_score : nat
}.

Definition total_score (o : OrganFailureAssessment) : nat :=
  resp_score o + cv_score o + hep_score o + coag_score o +
  renal_score_val o + neuro_score o.

Definition organ_systems_failing (o : OrganFailureAssessment) : nat :=
  (if organ_fail_th <=? resp_score o then 1 else 0) +
  (if organ_fail_th <=? cv_score o then 1 else 0) +
  (if organ_fail_th <=? hep_score o then 1 else 0) +
  (if organ_fail_th <=? coag_score o then 1 else 0) +
  (if organ_fail_th <=? renal_score_val o then 1 else 0) +
  (if organ_fail_th <=? neuro_score o then 1 else 0).

Definition multiorgan_dysfunction (o : OrganFailureAssessment) : bool :=
  organ_fail_th <=? organ_systems_failing o.

Lemma mods_requires_two_organs : forall o,
  multiorgan_dysfunction o = true -> 2 <= organ_systems_failing o.
Proof.
  intros o H. unfold multiorgan_dysfunction in H.
  apply Nat.leb_le in H. exact H.
Qed.

End NeonatalOrganFailure.

Module DifferentialDiagnosis.

(* Differential diagnosis for neonatal GI emergencies
   Key distinctions: NEC vs SIP vs sepsis without GI involvement vs surgical abdomen *)

Inductive GIDifferential : Type :=
  | NEC : GIDifferential
  | SpontaneousIntestinalPerforation : GIDifferential
  | Sepsis : GIDifferential
  | Volvulus : GIDifferential
  | HirschsprungDisease : GIDifferential
  | MeconiumIleus : GIDifferential
  | IntestinalAtresia : GIDifferential
  | FeedingIntolerance : GIDifferential.

(* Clinical presentation patterns *)
Record DifferentialFeatures : Type := MkDifferentialFeatures {
  has_pneumatosis : bool;
  has_portal_venous_gas : bool;
  has_pneumoperitoneum : bool;
  has_preceding_feeding_intolerance : bool;
  bilious_emesis : bool;
  sudden_distension : bool;
  has_abdominal_findings : bool;
  positive_blood_culture : bool;
  extremely_preterm : bool
}.

Definition suggests_nec (f : DifferentialFeatures) : bool :=
  has_pneumatosis f || has_portal_venous_gas f || has_preceding_feeding_intolerance f.

(* SIP requires perforation without pathognomonic NEC radiographics.
   Mild feeding intolerance no longer excludes SIP — common in preterms. *)
Definition suggests_sip (f : DifferentialFeatures) : bool :=
  has_pneumoperitoneum f &&
  negb (has_pneumatosis f) &&
  negb (has_portal_venous_gas f) &&
  extremely_preterm f.

Definition suggests_volvulus (f : DifferentialFeatures) : bool :=
  bilious_emesis f && sudden_distension f.

Definition suggests_sepsis_without_nec (f : DifferentialFeatures) : bool :=
  positive_blood_culture f && negb (has_abdominal_findings f).

(* Differential confidence scoring *)
Definition nec_confidence (f : DifferentialFeatures) : nat :=
  (if has_pneumatosis f then 5 else 0) +          (* pathognomonic *)
  (if has_portal_venous_gas f then 4 else 0) +    (* highly specific *)
  (if has_preceding_feeding_intolerance f then 2 else 0) +
  (if has_pneumoperitoneum f && has_pneumatosis f then 3 else 0).

Definition sip_confidence (f : DifferentialFeatures) : nat :=
  (if has_pneumoperitoneum f then 3 else 0) +
  (if negb (has_pneumatosis f) then 2 else 0) +
  (if negb (has_portal_venous_gas f) then 1 else 0) +
  (if extremely_preterm f then 2 else 0).

Definition most_likely_diagnosis (f : DifferentialFeatures) : GIDifferential :=
  if has_pneumatosis f then NEC
  else if suggests_volvulus f then Volvulus
  else if suggests_sepsis_without_nec f then Sepsis
  else if sip_confidence f <? nec_confidence f then NEC
  else if nec_confidence f <? sip_confidence f then SpontaneousIntestinalPerforation
  else if has_preceding_feeding_intolerance f then NEC
  else if suggests_sip f then SpontaneousIntestinalPerforation
  else FeedingIntolerance.

Lemma pneumatosis_implies_nec : forall f,
  has_pneumatosis f = true -> most_likely_diagnosis f = NEC.
Proof.
  intros f H. unfold most_likely_diagnosis. rewrite H. reflexivity.
Qed.

Lemma sip_requires_perforation : forall f,
  suggests_sip f = true -> has_pneumoperitoneum f = true.
Proof.
  intros f H. unfold suggests_sip in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H2 _].
  apply andb_true_iff in H2. destruct H2 as [H3 _].
  exact H3.
Qed.

End DifferentialDiagnosis.

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

Definition recommended_regimen_by_stage (s : Stage.t) : Regimen :=
  match s with
  | Stage.IA | Stage.IB => Empiric_AmpGent
  | Stage.IIA | Stage.IIB => Empiric_AmpGentMetro
  | Stage.IIIA | Stage.IIIB => Broad_VancMeropenem
  end.

Definition duration_days (s : Stage.t) : nat :=
  match s with
  | Stage.IA | Stage.IB => 3
  | Stage.IIA | Stage.IIB => 10
  | Stage.IIIA | Stage.IIIB => 14
  end.

Lemma advanced_nec_has_anaerobic_coverage : forall s,
  Stage.to_nat s >= 5 ->
  has_anaerobic_coverage (recommended_regimen_by_stage s) = true.
Proof.
  intros s H. destruct s; simpl in *; try lia; reflexivity.
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

(* NPO durations from ClinicalParameters (Walsh-Kliegman 1986) *)
Definition npo_stage_I : nat :=
  ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_I.
Definition npo_stage_II : nat :=
  ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_II.
Definition npo_stage_III : nat :=
  ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_III.

Definition npo_duration_by_stage (stage_nat : nat) : nat :=
  match stage_nat with
  | 1 | 2 => npo_stage_I
  | 3 | 4 => npo_stage_II
  | 5 => npo_stage_III
  | _ => npo_stage_III
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

(* Clinical trajectory represents the direction of change *)
Inductive ClinicalTrajectory : Type :=
  | Stable : ClinicalTrajectory
  | Improving : ClinicalTrajectory
  | Worsening : ClinicalTrajectory
  | RapidDeterioration : ClinicalTrajectory.

(* Trajectory severity for comparisons *)
Definition trajectory_severity (t : ClinicalTrajectory) : nat :=
  match t with
  | Improving => 0
  | Stable => 1
  | Worsening => 2
  | RapidDeterioration => 3
  end.

Definition trajectory_leb (t1 t2 : ClinicalTrajectory) : bool :=
  trajectory_severity t1 <=? trajectory_severity t2.

(* Rate of change categories *)
Inductive ChangeRate : Type :=
  | NoChange : ChangeRate
  | SlowChange : ChangeRate
  | ModerateChange : ChangeRate
  | RapidChange : ChangeRate.

Definition rate_to_nat (r : ChangeRate) : nat :=
  match r with
  | NoChange => 0
  | SlowChange => 1
  | ModerateChange => 2
  | RapidChange => 3
  end.

(* Management phases in clinical course *)
Inductive ManagementPhase : Type :=
  | Recognition : ManagementPhase
  | Stabilization : ManagementPhase
  | ActiveTreatment : ManagementPhase
  | SurgicalEvaluation : ManagementPhase
  | PostOperative : ManagementPhase
  | Recovery : ManagementPhase
  | Resolved : ManagementPhase
  | Death : ManagementPhase.

Definition phase_to_nat (p : ManagementPhase) : nat :=
  match p with
  | Recognition => 1
  | Stabilization => 2
  | ActiveTreatment => 3
  | SurgicalEvaluation => 4
  | PostOperative => 5
  | Recovery => 6
  | Resolved => 7
  | Death => 8
  end.

(* Time point captures state at a moment *)
Record TimePoint : Type := MkTimePoint {
  hours_since_onset : nat;
  current_phase : ManagementPhase;
  trajectory : ClinicalTrajectory;
  stage_at_timepoint : nat
}.

(* Temporal delta between two time points *)
Record TemporalDelta : Type := MkTemporalDelta {
  delta_hours : nat;
  stage_change : Z;            (* positive = worsening, negative = improving *)
  phase_changed : bool;
  trajectory_at_delta : ClinicalTrajectory
}.

(* Compute delta between two time points *)
Definition compute_delta (earlier later : TimePoint) : TemporalDelta :=
  MkTemporalDelta
    (hours_since_onset later - hours_since_onset earlier)
    (Z.of_nat (stage_at_timepoint later) - Z.of_nat (stage_at_timepoint earlier))
    (negb (phase_to_nat (current_phase earlier) =? phase_to_nat (current_phase later)))
    (trajectory later).

(* Determine trajectory from stage change and time *)
Definition infer_trajectory (stage_delta : Z) (hours : nat) : ClinicalTrajectory :=
  if (stage_delta >? 0)%Z then
    if hours <? 6 then RapidDeterioration
    else Worsening
  else if (stage_delta <? 0)%Z then Improving
  else Stable.

(* Velocity: stages per 24 hours (scaled by 10 for precision) *)
Definition stage_velocity_x10 (delta : TemporalDelta) : Z :=
  if delta_hours delta =? 0 then 0%Z
  else ((stage_change delta * 240) / Z.of_nat (delta_hours delta))%Z.

(* Threshold for rapid deterioration: >1 stage per 12 hours *)
Definition is_rapid_deterioration (delta : TemporalDelta) : bool :=
  (stage_velocity_x10 delta >? 20)%Z.

Definition valid_transition (from to : ManagementPhase) : bool :=
  match from, to with
  | Recognition, Stabilization => true
  | Stabilization, ActiveTreatment => true
  | ActiveTreatment, SurgicalEvaluation => true
  | ActiveTreatment, Recovery => true
  | ActiveTreatment, Death => true
  | SurgicalEvaluation, PostOperative => true
  | SurgicalEvaluation, ActiveTreatment => true
  | SurgicalEvaluation, Death => true
  | PostOperative, Recovery => true
  | PostOperative, Death => true
  | Recovery, Resolved => true
  | p1, p2 => phase_to_nat p1 =? phase_to_nat p2
  end.

Definition deterioration_triggers_escalation (t : ClinicalTrajectory) : bool :=
  match t with
  | Worsening => true
  | RapidDeterioration => true
  | _ => false
  end.

(* Reassessment interval in hours, shortened for higher stages *)
Definition hours_to_reassess (stage_nat : nat) (traj : ClinicalTrajectory) : nat :=
  let base := match traj with
              | RapidDeterioration => 2
              | Worsening => 4
              | Stable => 6
              | Improving => 12
              end in
  if 5 <=? stage_nat then (* Stage III *)
    Nat.max 1 (base / 2)
  else if 3 <=? stage_nat then (* Stage II *)
    base
  else (* Stage I *)
    Nat.min 12 (base + 2)
  .

Lemma rapid_deterioration_frequent_reassess :
  hours_to_reassess 5 RapidDeterioration = 1.
Proof. reflexivity. Qed.

Lemma transition_recognition_to_stabilization :
  valid_transition Recognition Stabilization = true.
Proof. reflexivity. Qed.

Definition is_terminal_phase (p : ManagementPhase) : bool :=
  match p with
  | Resolved => true
  | Death => true
  | _ => false
  end.

(* Reachability via transitive closure of valid_transition *)
Inductive reachable : ManagementPhase -> ManagementPhase -> Prop :=
  | reach_refl : forall p, reachable p p
  | reach_step : forall p1 p2 p3,
      valid_transition p1 p2 = true ->
      reachable p2 p3 ->
      reachable p1 p3.

(* Key reachability proofs *)
Lemma recognition_reaches_resolved :
  reachable Recognition Resolved.
Proof.
  apply reach_step with Stabilization. reflexivity.
  apply reach_step with ActiveTreatment. reflexivity.
  apply reach_step with Recovery. reflexivity.
  apply reach_step with Resolved. reflexivity.
  apply reach_refl.
Qed.

Lemma recognition_reaches_death :
  reachable Recognition Death.
Proof.
  apply reach_step with Stabilization. reflexivity.
  apply reach_step with ActiveTreatment. reflexivity.
  apply reach_step with Death. reflexivity.
  apply reach_refl.
Qed.

Lemma surgical_path_reaches_resolved :
  reachable SurgicalEvaluation Resolved.
Proof.
  apply reach_step with PostOperative. reflexivity.
  apply reach_step with Recovery. reflexivity.
  apply reach_step with Resolved. reflexivity.
  apply reach_refl.
Qed.

Lemma terminal_is_terminal : forall p,
  is_terminal_phase p = true -> reachable p p.
Proof.
  intros p _. apply reach_refl.
Qed.

(* All starting phases can reach a terminal phase *)
Theorem all_paths_terminate : forall p,
  reachable p Resolved \/ reachable p Death.
Proof.
  intros p.
  destruct p.
  - left. exact recognition_reaches_resolved.
  - left.
    apply reach_step with ActiveTreatment. reflexivity.
    apply reach_step with Recovery. reflexivity.
    apply reach_step with Resolved. reflexivity.
    apply reach_refl.
  - left.
    apply reach_step with Recovery. reflexivity.
    apply reach_step with Resolved. reflexivity.
    apply reach_refl.
  - left. exact surgical_path_reaches_resolved.
  - left.
    apply reach_step with Recovery. reflexivity.
    apply reach_step with Resolved. reflexivity.
    apply reach_refl.
  - left.
    apply reach_step with Resolved. reflexivity.
    apply reach_refl.
  - left. apply reach_refl.
  - right. apply reach_refl.
Qed.

End TemporalProgression.

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
  labs : option LabValues.t;
  coag : option CoagulationPanel.t;
  micro : Microbiology.t;
  vitals : option VitalSigns.t;
  systemic : SystemicSigns.t;
  intestinal : IntestinalSigns.t;
  radiographic : RadiographicSigns.t;
  hours_since_symptom_onset : nat
}.

Definition default_risk_factors : RiskFactors.t :=
  RiskFactors.MkRiskFactors 40 3500 false false false false false false.

Definition default_labs : LabValues.t :=
  LabValues.MkLabValues 10 5000 200 5 2 15 740 0 40 80.

(* Normal coagulation: PT 12 sec, INR 1.0, fibrinogen 250, iCa 1.15 *)
Definition default_coag : CoagulationPanel.t :=
  CoagulationPanel.MkCoagPanel 120 100 250 115.

Definition default_micro : Microbiology.t :=
  Microbiology.none.

Definition default_vitals : VitalSigns.t := VitalSigns.normal.

Definition empty : t :=
  MkClinicalState
    default_risk_factors
    (Some default_labs)
    (Some default_coag)
    default_micro
    (Some default_vitals)
    SystemicSigns.none
    IntestinalSigns.none
    RadiographicSigns.none
    0.

Definition is_high_risk_patient (c : t) : bool :=
  RiskFactors.high_risk (risk_factors c).

Definition has_lab_derangements (c : t) : bool :=
  match labs c with
  | Some l => LabValues.sepsis_markers_elevated l ||
              LabValues.thrombocytopenia l ||
              LabValues.metabolic_acidosis l
  | None => false
  end.

Definition has_coagulopathy (c : t) : bool :=
  match coag c with
  | Some cp => CoagulationPanel.coagulopathy_present cp
  | None => false
  end.

Definition has_dic (c : t) : bool :=
  match coag c, labs c with
  | Some cp, Some l =>
      CoagulationPanel.dic_criteria_met cp
        (LabValues.severe_thrombocytopenia l)
        (LabValues.elevated_lactate l)
  | _, _ => false
  end.

(* Effective hypotension: vitals-derived (MAP < GA weeks) when available,
   otherwise falls back to SystemicSigns.hypotension bool *)
Definition effective_hypotension (c : t) : bool :=
  match vitals c with
  | Some v => VitalSigns.hypotension v (RiskFactors.gestational_age_weeks (risk_factors c))
  | None => SystemicSigns.hypotension (systemic c)
  end.

Definition has_positive_blood_culture (c : t) : bool :=
  Microbiology.blood_culture_positive (micro c).

Definition has_gram_negative_sepsis (c : t) : bool :=
  Microbiology.gram_negative_sepsis (micro c).

(* Lab-derived systemic sign equivalents for classify_stage *)
Definition lab_metabolic_acidosis (c : t) : bool :=
  match labs c with
  | Some l => LabValues.metabolic_acidosis l
  | None => false
  end.

Definition lab_thrombocytopenia (c : t) : bool :=
  match labs c with
  | Some l => LabValues.thrombocytopenia l
  | None => false
  end.

Definition lab_neutropenia (c : t) : bool :=
  match labs c with
  | Some l => LabValues.neutropenia l
  | None => false
  end.

Definition overall_severity_score (c : t) : nat :=
  RiskFactors.risk_score (risk_factors c) +
  (match labs c with Some l => LabValues.lab_severity_score l | None => 0 end) +
  SystemicSigns.severity_score (systemic c) +
  (if has_coagulopathy c then 2 else 0) +
  (if has_dic c then 3 else 0) +
  (if has_positive_blood_culture c then 2 else 0).

End ClinicalState.

Module TimeSeries.

(* An observation is a clinical state at a specific time *)
Record Observation : Type := MkObservation {
  obs_time_hours : nat;
  obs_state : ClinicalState.t;
  obs_stage : nat;                          (* cached stage 1-6 *)
  obs_severity : nat                        (* cached severity score *)
}.

(* Create observation from clinical state *)
Definition make_observation (time_h : nat) (state : ClinicalState.t) (stage : nat) : Observation :=
  MkObservation time_h state stage (ClinicalState.overall_severity_score state).

(* A patient time series is a list of observations, newest first *)
Definition PatientTimeSeries := list Observation.

(* Time series must be ordered by time *)
Fixpoint is_time_ordered (ts : PatientTimeSeries) : bool :=
  match ts with
  | [] => true
  | [_] => true
  | o1 :: ((o2 :: _) as rest) =>
      (obs_time_hours o2 <=? obs_time_hours o1) && is_time_ordered rest
  end.

(* Get latest observation *)
Definition latest (ts : PatientTimeSeries) : option Observation :=
  match ts with
  | [] => None
  | o :: _ => Some o
  end.

(* Get earliest observation *)
Fixpoint earliest (ts : PatientTimeSeries) : option Observation :=
  match ts with
  | [] => None
  | [o] => Some o
  | _ :: rest => earliest rest
  end.

(* Number of observations *)
Definition series_length (ts : PatientTimeSeries) : nat := length ts.

(* Duration from first to last observation *)
Definition series_duration (ts : PatientTimeSeries) : nat :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_time_hours l - obs_time_hours e
  | _, _ => 0
  end.

(* Stage at a given observation index (0 = latest) *)
Definition stage_at_index (ts : PatientTimeSeries) (idx : nat) : option nat :=
  match nth_error ts idx with
  | Some o => Some (obs_stage o)
  | None => None
  end.

(* Compute stage change between two indices *)
Definition stage_change (ts : PatientTimeSeries) (earlier_idx later_idx : nat) : option Z :=
  match stage_at_index ts later_idx, stage_at_index ts earlier_idx with
  | Some s2, Some s1 => Some (Z.of_nat s2 - Z.of_nat s1)%Z
  | _, _ => None
  end.

(* Determine if patient is worsening (latest stage > earliest stage) *)
Definition is_worsening (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage e <? obs_stage l
  | _, _ => false
  end.

(* Determine if patient is improving *)
Definition is_improving (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage l <? obs_stage e
  | _, _ => false
  end.

(* Determine if patient is stable *)
Definition is_stable (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage l =? obs_stage e
  | _, _ => true
  end.

(* Count stage escalations in time series *)
Fixpoint count_escalations (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (if obs_stage o2 <? obs_stage o1 then 1 else 0) + count_escalations rest
  end.

(* Count stage improvements in time series *)
Fixpoint count_improvements (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (if obs_stage o1 <? obs_stage o2 then 1 else 0) + count_improvements rest
  end.

(* Maximum stage reached in series *)
Fixpoint max_stage (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] => 0
  | [o] => obs_stage o
  | o :: rest => Nat.max (obs_stage o) (max_stage rest)
  end.

(* Minimum stage in series *)
Fixpoint min_stage (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] => 0
  | [o] => obs_stage o
  | o :: rest => Nat.min (obs_stage o) (min_stage rest)
  end.

(* Stage range (max - min) *)
Definition stage_range (ts : PatientTimeSeries) : nat :=
  max_stage ts - min_stage ts.

(* Compute trajectory from time series.
   Uses max_stage to detect non-monotonic paths: if the patient peaked
   higher than their current stage, the trajectory reflects the peak-to-
   current relationship, not just the endpoint-to-endpoint delta. *)
Definition compute_trajectory (ts : PatientTimeSeries) : TemporalProgression.ClinicalTrajectory :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      let current := obs_stage l in
      let peak := max_stage ts in
      let stage_delta := (Z.of_nat current - Z.of_nat (obs_stage e))%Z in
      let duration := obs_time_hours l - obs_time_hours e in
      if current <? peak then
        (* Patient peaked higher then improved — net trajectory depends on
           whether current is still above baseline *)
        if (stage_delta >? 0)%Z then TemporalProgression.Worsening
        else if (stage_delta <? 0)%Z then TemporalProgression.Improving
        else TemporalProgression.Stable
      else
      let velocity := if duration =? 0 then 0%Z
                      else ((stage_delta * 240) / Z.of_nat duration)%Z in
      if (velocity >? 20)%Z then TemporalProgression.RapidDeterioration
      else if (stage_delta >? 0)%Z then TemporalProgression.Worsening
      else if (stage_delta <? 0)%Z then TemporalProgression.Improving
      else TemporalProgression.Stable
  | _, _ => TemporalProgression.Stable
  end.

(* Rate of change: stages per 24 hours (x10 for precision) *)
Definition stage_velocity_x10 (ts : PatientTimeSeries) : Z :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      let stage_delta := (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e))%Z in
      let duration := obs_time_hours l - obs_time_hours e in
      if duration =? 0 then 0%Z
      else ((stage_delta * 240) / Z.of_nat duration)%Z
  | _, _ => 0%Z
  end.

(* Severity trend: positive = worsening, negative = improving *)
Definition severity_trend (ts : PatientTimeSeries) : Z :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      (Z.of_nat (obs_severity l) - Z.of_nat (obs_severity e))%Z
  | _, _ => 0%Z
  end.

(* Check if any observation reached Stage IIIB (stage 6) *)
Definition reached_stage_IIIB (ts : PatientTimeSeries) : bool :=
  6 <=? max_stage ts.

(* Check if surgical threshold was crossed *)
Definition crossed_surgical_threshold (ts : PatientTimeSeries) : bool :=
  match earliest ts with
  | Some e => (obs_stage e <? 6) && reached_stage_IIIB ts
  | None => false
  end.

(* Find first observation at or above a stage threshold *)
Fixpoint first_at_stage (ts : PatientTimeSeries) (threshold : nat) : option Observation :=
  match ts with
  | [] => None
  | o :: rest =>
      match first_at_stage rest threshold with
      | Some found => Some found
      | None => if threshold <=? obs_stage o then Some o else None
      end
  end.

(* Time to reach a given stage (None if never reached) *)
Definition time_to_stage (ts : PatientTimeSeries) (threshold : nat) : option nat :=
  match first_at_stage ts threshold, earliest ts with
  | Some target, Some start => Some (obs_time_hours target - obs_time_hours start)
  | _, _ => None
  end.

(* Add observation to time series; rejects if out of order (newest first) *)
Definition add_observation (obs : Observation) (ts : PatientTimeSeries) : option PatientTimeSeries :=
  match ts with
  | [] => Some [obs]
  | prev :: _ =>
      if obs_time_hours prev <=? obs_time_hours obs then Some (obs :: ts)
      else None
  end.

(* Proofs about time series properties *)

Lemma empty_series_stable : compute_trajectory [] = TemporalProgression.Stable.
Proof. reflexivity. Qed.

Lemma singleton_series_stable : forall o,
  compute_trajectory [o] = TemporalProgression.Stable.
Proof.
  intros o. unfold compute_trajectory, latest, earliest, max_stage. simpl.
  rewrite Nat.ltb_irrefl. rewrite Z.sub_diag. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma worsening_implies_not_improving : forall ts,
  is_time_ordered ts = true ->
  is_worsening ts = true -> is_improving ts = false.
Proof.
  intros ts _ H.
  unfold is_worsening, is_improving in *.
  destruct (latest ts) as [l|]; destruct (earliest ts) as [e|]; try discriminate.
  apply Nat.ltb_lt in H.
  apply Nat.ltb_ge. lia.
Qed.

Lemma stable_implies_no_escalations_single : forall o,
  count_escalations [o] = 0.
Proof. reflexivity. Qed.

Lemma max_stage_ge_latest : forall ts o,
  latest ts = Some o -> obs_stage o <= max_stage ts.
Proof.
  intros ts o H.
  destruct ts as [|o' rest].
  - discriminate.
  - simpl in H. inversion H. subst. simpl.
    destruct rest as [|o2 rest2].
    + lia.
    + apply Nat.le_max_l.
Qed.

Lemma reached_IIIB_implies_max_ge_6 : forall ts,
  reached_stage_IIIB ts = true -> 6 <= max_stage ts.
Proof.
  intros ts H. unfold reached_stage_IIIB in H.
  apply Nat.leb_le in H. exact H.
Qed.

End TimeSeries.

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
  let effective_stage3_sys := SystemicSigns.stage3_signs sys
    || ClinicalState.effective_hypotension c
    || ClinicalState.has_dic c
    || ClinicalState.lab_neutropenia c in
  let effective_stage2b_sys := SystemicSigns.stage2b_signs sys
    || ClinicalState.lab_metabolic_acidosis c
    || ClinicalState.lab_thrombocytopenia c in
  if RadiographicSigns.pneumoperitoneum rad then Stage.IIIB
  else if effective_stage3_sys && IntestinalSigns.stage3_signs int && (RadiographicSigns.stage2a_findings rad || RadiographicSigns.stage2b_findings rad) then Stage.IIIA
  else if (effective_stage2b_sys || IntestinalSigns.stage2b_signs int) && IntestinalSigns.stage2_signs int && RadiographicSigns.stage2b_findings rad then Stage.IIB
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

(* Trajectory-aware classification using time series *)

(* Classify based on latest observation in time series *)
Definition classify_from_series (ts : TimeSeries.PatientTimeSeries) : option Stage.t :=
  match TimeSeries.latest ts with
  | Some obs => Some (classify (TimeSeries.obs_state obs))
  | None => None
  end.

(* Get trajectory-adjusted urgency level *)
Inductive UrgencyLevel : Type :=
  | Routine : UrgencyLevel
  | Elevated : UrgencyLevel
  | Urgent : UrgencyLevel
  | Emergent : UrgencyLevel.

Definition urgency_from_trajectory (traj : TemporalProgression.ClinicalTrajectory)
    (current_stage : Stage.t) : UrgencyLevel :=
  match traj, current_stage with
  | TemporalProgression.RapidDeterioration, _ => Emergent
  | TemporalProgression.Worsening, Stage.IIIA => Emergent
  | TemporalProgression.Worsening, Stage.IIB => Urgent
  | TemporalProgression.Worsening, _ => Elevated
  | TemporalProgression.Stable, Stage.IIIA => Urgent
  | TemporalProgression.Stable, Stage.IIIB => Emergent
  | TemporalProgression.Stable, _ => Routine
  | TemporalProgression.Improving, _ => Routine
  end.

(* Classify with trajectory context *)
Record TrajectoryAwareClassification : Type := MkTrajectoryAware {
  tac_stage : Stage.t;
  tac_trajectory : TemporalProgression.ClinicalTrajectory;
  tac_urgency : UrgencyLevel;
  tac_escalation_count : nat;
  tac_hours_at_current_stage : nat
}.

Definition classify_with_trajectory (ts : TimeSeries.PatientTimeSeries)
    : option TrajectoryAwareClassification :=
  match TimeSeries.latest ts with
  | Some obs =>
      let stage := classify (TimeSeries.obs_state obs) in
      let traj := TimeSeries.compute_trajectory ts in
      let urg := urgency_from_trajectory traj stage in
      let esc := TimeSeries.count_escalations ts in
      let hrs := match TimeSeries.first_at_stage ts (Stage.to_nat stage) with
                 | Some first_obs =>
                     TimeSeries.obs_time_hours obs - TimeSeries.obs_time_hours first_obs
                 | None => 0
                 end in
      Some (MkTrajectoryAware stage traj urg esc hrs)
  | None => None
  end.

(* Determine if escalation of care is warranted based on trajectory *)
Definition escalation_warranted (ts : TimeSeries.PatientTimeSeries) : bool :=
  match classify_with_trajectory ts with
  | Some tac =>
      match tac_urgency tac with
      | Emergent => true
      | Urgent => true
      | _ => false
      end
  | None => false
  end.

(* Recommend reassessment interval based on trajectory *)
Definition recommended_reassess_hours (ts : TimeSeries.PatientTimeSeries) : nat :=
  match classify_with_trajectory ts with
  | Some tac =>
      match tac_urgency tac with
      | Emergent => 1
      | Urgent => 2
      | Elevated => 4
      | Routine => 8
      end
  | None => 8
  end.

Lemma rapid_deterioration_always_emergent : forall stage,
  urgency_from_trajectory TemporalProgression.RapidDeterioration stage = Emergent.
Proof. intros []; reflexivity. Qed.

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

Module SurgicalProcedures.

Inductive Procedure : Type :=
  | PrimaryPeritonealDrainage : Procedure
  | ExploratoryLaparotomy : Procedure
  | BowelResectionPrimaryAnastomosis : Procedure
  | BowelResectionStoma : Procedure
  | SecondLookLaparotomy : Procedure
  | StomaReversal : Procedure.

Inductive Urgency : Type :=
  | Emergent : Urgency
  | Urgent : Urgency
  | Elective : Urgency.

Definition procedure_urgency (p : Procedure) : Urgency :=
  match p with
  | PrimaryPeritonealDrainage => Emergent
  | ExploratoryLaparotomy => Emergent
  | BowelResectionPrimaryAnastomosis => Urgent
  | BowelResectionStoma => Urgent
  | SecondLookLaparotomy => Urgent
  | StomaReversal => Elective
  end.

Definition initial_procedure_for_perforation (birth_weight_grams : nat) : Procedure :=
  if birth_weight_grams <? 1000 then PrimaryPeritonealDrainage
  else ExploratoryLaparotomy.

Definition requires_stoma (extent_of_necrosis_percent : nat) : bool :=
  50 <? extent_of_necrosis_percent.

Lemma elbw_gets_drain : forall bw,
  bw < 1000 -> initial_procedure_for_perforation bw = PrimaryPeritonealDrainage.
Proof.
  intros bw H. unfold initial_procedure_for_perforation.
  destruct (bw <? 1000) eqn:E.
  - reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

End SurgicalProcedures.

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
    (Some abnormal_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some abnormal_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some ClinicalState.default_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some ClinicalState.default_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some abnormal_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some abnormal_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
    stage_IIIA_witness_systemic
    stage_IIIA_witness_intestinal
    stage_IIIA_witness_radiographic
    36.

Lemma stage_IIIA_witness_classifies_correctly :
  Classification.classify stage_IIIA_witness = Stage.IIIA.
Proof. reflexivity. Qed.

(* Time series witness examples *)

(* Observation at hour 0: Stage IA *)
Definition obs_hour_0 : TimeSeries.Observation :=
  TimeSeries.MkObservation 0 stage_IA_witness 1 5.

(* Observation at hour 6: Stage IIA (worsening) *)
Definition obs_hour_6 : TimeSeries.Observation :=
  TimeSeries.MkObservation 6 stage_IIA_witness 3 12.

(* Observation at hour 12: Stage IIB (continued worsening) *)
Definition obs_hour_12 : TimeSeries.Observation :=
  TimeSeries.MkObservation 12 stage_IIB_witness 4 15.

(* Observation at hour 24: Stage IIIA (severe) *)
Definition obs_hour_24 : TimeSeries.Observation :=
  TimeSeries.MkObservation 24 stage_IIIA_witness 5 18.

(* Time series showing progressive deterioration over 24 hours *)
Definition deteriorating_series : TimeSeries.PatientTimeSeries :=
  [obs_hour_24; obs_hour_12; obs_hour_6; obs_hour_0].

(* Time series showing stable course *)
Definition stable_series : TimeSeries.PatientTimeSeries :=
  [obs_hour_6; TimeSeries.MkObservation 3 stage_IIA_witness 3 12;
   TimeSeries.MkObservation 0 stage_IIA_witness 3 11].

Lemma deteriorating_series_is_worsening :
  TimeSeries.is_worsening deteriorating_series = true.
Proof. reflexivity. Qed.

(* 4 stages in 24h = velocity 40 > 20 threshold = RapidDeterioration *)
Lemma deteriorating_series_trajectory :
  TimeSeries.compute_trajectory deteriorating_series = TemporalProgression.RapidDeterioration.
Proof. reflexivity. Qed.

Lemma deteriorating_series_escalation_count :
  TimeSeries.count_escalations deteriorating_series = 3.
Proof. reflexivity. Qed.

Lemma stable_series_is_stable :
  TimeSeries.is_stable stable_series = true.
Proof. reflexivity. Qed.

Lemma stable_series_trajectory :
  TimeSeries.compute_trajectory stable_series = TemporalProgression.Stable.
Proof. reflexivity. Qed.

Lemma deteriorating_max_stage :
  TimeSeries.max_stage deteriorating_series = 5.
Proof. reflexivity. Qed.

Lemma deteriorating_series_duration :
  TimeSeries.series_duration deteriorating_series = 24.
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
    (Some ClinicalState.default_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
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
    (Some ClinicalState.default_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
    SystemicSigns.none
    IntestinalSigns.none
    RadiographicSigns.none
    0.

Lemma term_infant_not_high_risk :
  ClinicalState.is_high_risk_patient term_infant_low_risk = false.
Proof. reflexivity. Qed.

Lemma empty_state_diagnoses_not_nec :
  Classification.diagnose ClinicalState.empty = Diagnosis.NotNEC.
Proof. reflexivity. Qed.

Definition isolated_perforation_radiographic : RadiographicSigns.t :=
  RadiographicSigns.MkRadiographicSigns false false false false false false true.

Definition isolated_perforation : ClinicalState.t :=
  ClinicalState.MkClinicalState
    (RiskFactors.MkRiskFactors 25 700 false false false false false false)
    (Some ClinicalState.default_labs)
    (Some ClinicalState.default_coag)
    ClinicalState.default_micro
    None
    SystemicSigns.none
    IntestinalSigns.none
    isolated_perforation_radiographic
    2.

Lemma isolated_perforation_is_sip :
  Classification.diagnose isolated_perforation = Diagnosis.SuspectedSIP.
Proof. reflexivity. Qed.

Lemma isolated_perforation_stages_IIIB :
  Classification.classify isolated_perforation = Stage.IIIB.
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

Theorem pneumoperitoneum_maximal : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  forall s, Stage.to_nat s <= Stage.to_nat (Classification.classify c).
Proof.
  intros c Hperf s.
  rewrite (Classification.pneumoperitoneum_forces_IIIB c Hperf).
  destruct s; simpl; lia.
Qed.

Theorem stage_order_reflects_severity : forall s1 s2,
  Stage.to_nat s1 < Stage.to_nat s2 ->
  Treatment.npo_duration_days (Treatment.of_stage s1) <=
  Treatment.npo_duration_days (Treatment.of_stage s2).
Proof.
  intros s1 s2 H.
  destruct s1; destruct s2; simpl in *; try lia.
Qed.

(* Completeness: classify is total and deterministic *)
Theorem classify_total : forall c : ClinicalState.t,
  { s : Stage.t | Classification.classify c = s }.
Proof.
  intros c. exists (Classification.classify c). reflexivity.
Qed.

(* Stage enumeration is complete - every nat 1-6 corresponds to a stage *)
Theorem stage_enumeration_complete : forall n,
  1 <= n <= 6 -> exists s : Stage.t, Stage.to_nat s = n.
Proof.
  intros n [Hlo Hhi].
  destruct n as [|[|[|[|[|[|n']]]]]].
  - lia.
  - exists Stage.IA. reflexivity.
  - exists Stage.IB. reflexivity.
  - exists Stage.IIA. reflexivity.
  - exists Stage.IIB. reflexivity.
  - exists Stage.IIIA. reflexivity.
  - destruct n'; [exists Stage.IIIB; reflexivity | lia].
Qed.

(* Decidability: stage equality is decidable *)
Definition stage_eq_dec : forall s1 s2 : Stage.t, {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct s1; destruct s2;
  try (left; reflexivity);
  right; discriminate.
Defined.

(* Classification is decidable *)
Theorem classify_decidable : forall c s,
  {Classification.classify c = s} + {Classification.classify c <> s}.
Proof.
  intros c s. apply stage_eq_dec.
Qed.

(* Uniqueness: each patient has exactly one stage *)
Theorem classify_unique : forall c s1 s2,
  Classification.classify c = s1 ->
  Classification.classify c = s2 ->
  s1 = s2.
Proof.
  intros c s1 s2 H1 H2. rewrite <- H1. rewrite <- H2. reflexivity.
Qed.

(* Combined completeness statement *)
Theorem classification_complete_and_unique : forall c,
  exists! s, Classification.classify c = s.
Proof.
  intros c.
  exists (Classification.classify c).
  split.
  - reflexivity.
  - intros s' H. rewrite H. reflexivity.
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

(* Outcome statistics from:
   - Mortality: Fitzgibbons et al. 2009, Pediatrics 123(1):e58-66
     Overall NEC mortality 20-30%; Stage III approaches 30-50%
   - Stricture: Horwitz et al. 1995, J Pediatr Surg 30(9):1314-1317
     Post-NEC stricture 10-35% depending on stage and extent
   - Short bowel syndrome: Cole et al. 2008, J Perinatol 28(12):812-817
     SBS in 9% of medical NEC, 23% of surgical NEC
   - Neurodevelopmental: Hintz et al. 2005, Pediatrics 115(3):696-703
     Surgical NEC associated with increased NDI risk (OR 1.5-2.0)

   Values below are midpoint estimates; actual rates vary by institution,
   gestational age, and era of data collection. *)

Inductive Outcome : Type :=
  | FullRecovery : Outcome
  | Stricture : Outcome
  | ShortBowelSyndrome : Outcome
  | Recurrence : Outcome
  | Death : Outcome.

(* Mortality: Stage I (suspected) has near-zero attributable mortality;
   Stage II 5-10%; Stage III 20-50% (Fitzgibbons 2009, Neu 2011) *)
Definition mortality_risk_percent (s : Stage.t) : nat :=
  match s with
  | Stage.IA => 0
  | Stage.IB => 0
  | Stage.IIA => 5
  | Stage.IIB => 10
  | Stage.IIIA => 20
  | Stage.IIIB => 30
  end.

(* Stricture rates increase with disease severity and surgical intervention
   (Horwitz 1995, Butter 2006 J Pediatr Surg 41:1632-1636) *)
Definition stricture_risk_percent (s : Stage.t) : nat :=
  match s with
  | Stage.IA => 0
  | Stage.IB => 0
  | Stage.IIA => 10
  | Stage.IIB => 20
  | Stage.IIIA => 25
  | Stage.IIIB => 35
  end.

(* Short bowel syndrome risk correlates with extent of resection
   (Cole 2008, Wales 2010 Semin Pediatr Surg 19:3-9) *)
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

Lemma higher_stage_worse_mortality : forall s1 s2,
  Stage.leb s1 s2 = true ->
  mortality_risk_percent s1 <= mortality_risk_percent s2.
Proof.
  intros s1 s2 H.
  destruct s1; destruct s2; simpl in *; try lia; try discriminate.
Qed.

Lemma higher_stage_worse_stricture : forall s1 s2,
  Stage.leb s1 s2 = true ->
  stricture_risk_percent s1 <= stricture_risk_percent s2.
Proof.
  intros s1 s2 H.
  destruct s1; destruct s2; simpl in *; try lia; try discriminate.
Qed.

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

(* IIIB: pneumoperitoneum is absolute indication, regardless of other findings *)
Definition stage_IIIB_criteria :=
  MkCriteria Stage.IIIB false 0 false 0 true 3.

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

(* Classification consistency analysis:
   classify_declarative uses threshold-based criteria matching
   Classification.classify_stage uses specific sign combinations

   Key invariant: both agree on Stage.IIIB when pneumoperitoneum present *)

Lemma classify_declarative_IIIB_on_perf : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_declarative c = Stage.IIIB.
Proof.
  intros c Hperf.
  unfold classify_declarative, meets_criteria, stage_IIIB_criteria.
  simpl.
  unfold compute_radiographic_level.
  rewrite Hperf. simpl.
  reflexivity.
Qed.

(* Both classifications agree on pneumoperitoneum -> IIIB *)
Lemma classify_agreement_on_perforation : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  Classification.classify c = Stage.IIIB /\ classify_declarative c = Stage.IIIB.
Proof.
  intros c Hperf. split.
  - apply Classification.pneumoperitoneum_forces_IIIB. exact Hperf.
  - apply classify_declarative_IIIB_on_perf. exact Hperf.
Qed.

(* Stage bounds are preserved *)
Lemma classify_declarative_bounded : forall c,
  1 <= Stage.to_nat (classify_declarative c) <= 6.
Proof.
  intros c. unfold classify_declarative.
  destruct (meets_criteria c stage_IIIB_criteria);
  destruct (meets_criteria c stage_IIIA_criteria);
  destruct (meets_criteria c stage_IIB_criteria);
  destruct (meets_criteria c stage_IIA_criteria);
  destruct (meets_criteria c stage_IB_criteria);
  simpl; lia.
Qed.

End BellCriteria.
