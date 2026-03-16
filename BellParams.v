From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

(* Naming convention: modules that define a single primary type use `t`
   (Coq stdlib style). Auxiliary record types within a module use
   descriptive names (e.g., MedicationRiskFactors, UltrasoundFindings).
   Both are accessed via module qualification. *)

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

(* Z-based risk score avoids nat underflow when protective > raw *)
Definition risk_score_Z (r : t) : Z :=
  (Z.of_nat (risk_score_raw r) - Z.of_nat (protective_factor r))%Z.

(* Nat accessor: clamps negative scores to 0 *)
Definition risk_score (r : t) : nat :=
  Z.to_nat (Z.max 0 (risk_score_Z r)).

(* high_risk uses the Z-score directly so that clinically distinct
   low-risk patients are not collapsed to the same nat by clamping. *)
Definition high_risk (r : t) : bool :=
  (6 <=? risk_score_Z r)%Z.

(* Backward-compatible nat accessor *)
Definition high_risk_nat (r : t) : bool :=
  6 <=? risk_score r.

(* Weight-for-gestational-age classification.
   SGA = birth weight < 10th percentile for GA.
   Simplified: <2500g at term, <1500g at 32 wk, <1000g at 28 wk.
   Kramer et al. 2001, Pediatrics 108(2):E35. *)
Inductive WeightForGA : Type :=
  | SGA : WeightForGA   (* small for gestational age *)
  | AGA : WeightForGA   (* appropriate for gestational age *)
  | LGA : WeightForGA.  (* large for gestational age *)

(* Approximate 10th/90th percentile thresholds by GA bracket *)
Definition classify_weight_for_ga (ga_weeks bw_grams : nat) : WeightForGA :=
  let p10 := if ga_weeks <? 28 then 700
             else if ga_weeks <? 32 then 1000
             else if ga_weeks <? 37 then 1800
             else 2500 in
  let p90 := if ga_weeks <? 28 then 1200
             else if ga_weeks <? 32 then 1800
             else if ga_weeks <? 37 then 3200
             else 4000 in
  if bw_grams <? p10 then SGA
  else if p90 <? bw_grams then LGA
  else AGA.

Definition is_sga (r : t) : bool :=
  match classify_weight_for_ga (gestational_age_weeks r) (birth_weight_grams r) with
  | SGA => true
  | _ => false
  end.

(* Postnatal age as risk factor.
   NEC incidence peaks at 30-31 weeks postmenstrual age.
   Neu & Walker 2011, NEJM 364:255-264. *)
Definition postmenstrual_age (ga_weeks day_of_life : nat) : nat :=
  ga_weeks + (day_of_life / 7).

Definition in_peak_nec_window (ga_weeks day_of_life : nat) : bool :=
  let pma := postmenstrual_age ga_weeks day_of_life in
  (29 <=? pma) && (pma <=? 33).

(* Pre-NEC feeding advancement rate as risk factor.
   Berseth et al. 2003, J Pediatr 143(4):500-505.
   Rapid advancement (>30 mL/kg/day) associated with increased NEC. *)
Definition rapid_feed_advancement_threshold : nat := 30.

(* Medication risk factors.
   - Indomethacin: Attridge et al. 2006, J Perinatol 26(2):93-100
   - H2 blockers: Guillet et al. 2006, Pediatrics 117(1):e137-e142
   - Antenatal steroids (protective): Roberts et al. 2017, Cochrane *)
Record MedicationRiskFactors : Type := MkMedRisk {
  received_indomethacin : bool;
  received_h2_blockers : bool;
  received_antenatal_steroids : bool   (* protective *)
}.

Definition medication_risk_score (m : MedicationRiskFactors) : nat :=
  (if received_indomethacin m then 2 else 0) +
  (if received_h2_blockers m then 1 else 0).

Definition medication_protective_score (m : MedicationRiskFactors) : nat :=
  if received_antenatal_steroids m then 1 else 0.

(* The Z score can go negative: a term breast-fed infant with no
   comorbidities has raw = 0, protective = 2, so Z score = -2. *)
Lemma risk_score_Z_can_be_negative :
  exists r, (risk_score_Z r < 0)%Z.
Proof.
  exists (MkRiskFactors 40 3500 false false false false false false).
  vm_compute. reflexivity.
Qed.

(* When Z score is negative, nat risk_score clamps to 0 *)
Lemma risk_score_nonneg_clamp : forall r,
  (risk_score_Z r < 0)%Z -> risk_score r = 0.
Proof.
  intros r H. unfold risk_score. rewrite Z.max_l; [reflexivity | lia].
Qed.

Lemma extremely_preterm_high_risk : forall r,
  extremely_preterm r = true ->
  extremely_low_birth_weight r = true ->
  high_risk r = true.
Proof.
  intros r Hp Hw. unfold high_risk, risk_score_Z,
    risk_score_raw, protective_factor.
  rewrite Hp, Hw. simpl.
  destruct (formula_fed r) eqn:Eff;
  destruct (history_of_perinatal_asphyxia r);
  destruct (congenital_heart_disease r);
  destruct (polycythemia r);
  destruct (umbilical_catheter r);
  destruct (exchange_transfusion r);
  vm_compute; reflexivity.
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

Definition coagulopathy_present (c : t) : bool :=
  pt_prolonged c || inr_elevated c || hypofibrinogenemia c.

Definition dic_criteria_met (c : t) (platelets_low : bool) (elevated_lactate : bool) : bool :=
  platelets_low && coagulopathy_present c && elevated_lactate.

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

(* Renamed from `none` to avoid collision when modules are opened *)
Definition no_cultures : t :=
  MkMicrobiology NotCollected None None NotCollected None None NotCollected None None.

(* Temporal ordering constraint.
   Enforces collected_h <= resulted_h for all culture types. *)
Definition temporally_ordered (m : t) : Prop :=
  (match blood_culture_collected_h m, blood_culture_resulted_h m with
   | Some c, Some r => c <= r
   | _, _ => True
   end) /\
  (match csf_culture_collected_h m, csf_culture_resulted_h m with
   | Some c, Some r => c <= r
   | _, _ => True
   end) /\
  (match peritoneal_culture_collected_h m, peritoneal_culture_resulted_h m with
   | Some c, Some r => c <= r
   | _, _ => True
   end).

Lemma no_cultures_temporally_ordered : temporally_ordered no_cultures.
Proof. unfold temporally_ordered, no_cultures. simpl. auto. Qed.

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

(* Gestational-age-dependent vital sign thresholds.
   Fleming et al. 2011, Lancet 377(9770):1011-1018.
   Tachycardia: >180 bpm term, >190 preterm; Bradycardia: <100 term, <80 preterm.
   Tachypnea: >60 term, >70 preterm (higher baseline RR in preterms). *)
Definition tachycardia_ga (v : t) (ga_weeks : nat) : bool :=
  if ga_weeks <? 32 then 190 <? heart_rate_bpm v
  else 180 <? heart_rate_bpm v.

Definition bradycardia_ga (v : t) (ga_weeks : nat) : bool :=
  if ga_weeks <? 32 then heart_rate_bpm v <? 80
  else heart_rate_bpm v <? 100.

Definition tachypnea_ga (v : t) (ga_weeks : nat) : bool :=
  if ga_weeks <? 32 then 70 <? respiratory_rate_bpm v
  else 60 <? respiratory_rate_bpm v.

(* Renamed from severity_score to avoid collision with SystemicSigns *)
Definition vitals_severity (v : t) : nat :=
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
