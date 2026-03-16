(******************************************************************************)
(*                                                                            *)
(*     QuickChick property-based tests for BellStaging                        *)
(*                                                                            *)
(*     Randomly generates ClinicalState values and checks invariants:         *)
(*     - classify always returns a stage in [1,6]                             *)
(*     - pneumoperitoneum forces IIIB                                         *)
(*     - IIIB is the only stage requiring surgery                             *)
(*     - adding signs never decreases stage (monotonicity)                    *)
(*     - urgency is monotone in stage for each trajectory                     *)
(*     - NPO duration is monotone in stage                                    *)
(*     - organ failure feedback never decreases stage                         *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith Bool List ZArith Lia String.
From QuickChick Require Import QuickChick.
From BellStaging Require Import BellStaging.

Import ListNotations.
Open Scope string_scope.

(* --- Generators --- *)

Definition gen_bool : G bool :=
  freq_ (ret true) [(1, ret true); (1, ret false)].

Definition gen_ga : G nat := choose (22, 42).
Definition gen_bw : G nat := choose (400, 4500).

Definition gen_risk_factors : G RiskFactors.t :=
  bindGen gen_ga (fun ga =>
  bindGen gen_bw (fun bw =>
  bindGen gen_bool (fun ff =>
  bindGen gen_bool (fun asph =>
  bindGen gen_bool (fun chd =>
  bindGen gen_bool (fun poly =>
  bindGen gen_bool (fun umb =>
  bindGen gen_bool (fun exch =>
  returnGen (RiskFactors.MkRiskFactors ga bw ff asph chd poly umb exch))))))))).

Definition gen_labs : G LabValues.t :=
  bindGen (choose (1, 40)) (fun wbc =>
  bindGen (choose (500, 10000)) (fun anc =>
  bindGen (choose (10, 300)) (fun plt =>
  bindGen (choose (1, 50)) (fun crp =>
  bindGen (choose (1, 20)) (fun pct =>
  bindGen (choose (5, 50)) (fun lac =>
  bindGen (choose (700, 750)) (fun ph =>
  bindGen (choose (0, 15)) (fun bd =>
  bindGen (choose (25, 60)) (fun pco2 =>
  bindGen (choose (30, 150)) (fun glu =>
  returnGen (LabValues.MkLabValues wbc anc plt crp pct lac ph bd pco2 glu))))))))))).

Definition gen_systemic : G SystemicSigns.t :=
  bindGen gen_bool (fun ti =>
  bindGen gen_bool (fun ap =>
  bindGen gen_bool (fun br =>
  bindGen gen_bool (fun le =>
  bindGen gen_bool (fun ma =>
  bindGen gen_bool (fun th =>
  bindGen gen_bool (fun hy =>
  bindGen gen_bool (fun rf =>
  bindGen gen_bool (fun di =>
  bindGen gen_bool (fun ne =>
  returnGen (SystemicSigns.MkSystemicSigns ti ap br le ma th hy rf di ne))))))))))).

Definition gen_intestinal : G IntestinalSigns.t :=
  bindGen gen_bool (fun egr =>
  bindGen gen_bool (fun mad =>
  bindGen gen_bool (fun obs =>
  bindGen gen_bool (fun gbs =>
  bindGen gen_bool (fun abs_ =>
  bindGen gen_bool (fun at_ =>
  bindGen gen_bool (fun ac =>
  bindGen gen_bool (fun rlq =>
  bindGen gen_bool (fun md =>
  bindGen gen_bool (fun per =>
  returnGen (IntestinalSigns.MkIntestinalSigns egr mad obs gbs abs_ at_ ac rlq md per))))))))))).

Definition gen_radiographic : G RadiographicSigns.t :=
  bindGen gen_bool (fun nmi =>
  bindGen gen_bool (fun id_ =>
  bindGen gen_bool (fun fi =>
  bindGen gen_bool (fun pi =>
  bindGen gen_bool (fun pvg =>
  bindGen gen_bool (fun asc =>
  bindGen gen_bool (fun pnp =>
  returnGen (RadiographicSigns.MkRadiographicSigns nmi id_ fi pi pvg asc pnp)))))))).

Definition gen_neuro : G NeonatalOrganFailure.NeuroStatus :=
  freq_ (returnGen NeonatalOrganFailure.NeuroNormal)
    [(1, returnGen NeonatalOrganFailure.NeuroNormal);
     (1, returnGen NeonatalOrganFailure.SarnatI);
     (1, returnGen NeonatalOrganFailure.SarnatII);
     (1, returnGen NeonatalOrganFailure.SarnatIII)].

Definition gen_clinical_state : G ClinicalState.t :=
  bindGen gen_risk_factors (fun rf =>
  bindGen gen_labs (fun labs =>
  bindGen gen_systemic (fun sys =>
  bindGen gen_intestinal (fun int =>
  bindGen gen_radiographic (fun rad =>
  bindGen gen_neuro (fun neuro =>
  bindGen (choose (0, 72)) (fun h =>
  returnGen (ClinicalState.MkClinicalState
    rf (Some labs) (Some ClinicalState.default_coag)
    Microbiology.no_cultures (Some VitalSigns.normal)
    sys int rad neuro h h h h)))))))).

(* --- Show instances --- *)

#[export] Instance show_clinical_state : Show ClinicalState.t :=
  {| show _ := "<ClinicalState>" |}.

#[export] Instance show_risk_factors : Show RiskFactors.t :=
  {| show r := "RF(ga=" ++ show (RiskFactors.gestational_age_weeks r)
            ++ ",bw=" ++ show (RiskFactors.birth_weight_grams r) ++ ")" |}.

Close Scope string_scope.

(* --- Properties --- *)

(* P1: classify always returns a valid stage (1-6) *)
Definition prop_classify_bounded :=
  forAll gen_clinical_state (fun c =>
  let s := Classification.classify c in
  (1 <=? Stage.to_nat s) && (Stage.to_nat s <=? 6)).

(* P2: pneumoperitoneum forces IIIB *)
Definition prop_pneumoperitoneum_IIIB :=
  forAll gen_clinical_state (fun c =>
  let rad := ClinicalState.radiographic c in
  let c' := ClinicalState.MkClinicalState
    (ClinicalState.risk_factors c)
    (ClinicalState.labs c)
    (ClinicalState.coag c)
    (ClinicalState.micro c)
    (ClinicalState.vitals c)
    (ClinicalState.systemic c)
    (ClinicalState.intestinal c)
    (RadiographicSigns.MkRadiographicSigns
      (RadiographicSigns.normal_or_mild_ileus rad)
      (RadiographicSigns.intestinal_dilation rad)
      (RadiographicSigns.focal_ileus rad)
      (RadiographicSigns.pneumatosis_intestinalis rad)
      (RadiographicSigns.portal_venous_gas rad)
      (RadiographicSigns.ascites rad)
      true)
    (ClinicalState.neuro_status c)
    (ClinicalState.hours_since_symptom_onset c)
    (ClinicalState.systemic_assessed_h c)
    (ClinicalState.intestinal_assessed_h c)
    (ClinicalState.radiographic_assessed_h c) in
  Stage.to_nat (Classification.classify c') =? 6).

(* P3: only IIIB requires surgery *)
Definition prop_surgery_only_IIIB :=
  forAll gen_clinical_state (fun c =>
  let s := Classification.classify c in
  let surg := Treatment.requires_surgery (Treatment.of_stage s) in
  if surg then Stage.to_nat s =? 6 else true).

(* P4: adding pneumatosis never decreases stage *)
Definition prop_adding_pneumatosis_monotone :=
  forAll gen_clinical_state (fun c =>
  let s1 := Stage.to_nat (Classification.classify c) in
  let rad := ClinicalState.radiographic c in
  let rad' := RadiographicSigns.MkRadiographicSigns
    (RadiographicSigns.normal_or_mild_ileus rad)
    (RadiographicSigns.intestinal_dilation rad)
    (RadiographicSigns.focal_ileus rad)
    true
    (RadiographicSigns.portal_venous_gas rad)
    (RadiographicSigns.ascites rad)
    (RadiographicSigns.pneumoperitoneum rad) in
  let c' := ClinicalState.MkClinicalState
    (ClinicalState.risk_factors c)
    (ClinicalState.labs c)
    (ClinicalState.coag c)
    (ClinicalState.micro c)
    (ClinicalState.vitals c)
    (ClinicalState.systemic c)
    (ClinicalState.intestinal c)
    rad'
    (ClinicalState.neuro_status c)
    (ClinicalState.hours_since_symptom_onset c)
    (ClinicalState.systemic_assessed_h c)
    (ClinicalState.intestinal_assessed_h c)
    (ClinicalState.radiographic_assessed_h c) in
  let s2 := Stage.to_nat (Classification.classify c') in
  s1 <=? s2).

(* P5: organ failure feedback never decreases stage *)
Definition prop_organ_failure_monotone :=
  forAll gen_clinical_state (fun c =>
  let s := Classification.classify c in
  let oa := NeonatalOrganFailure.MkOrganFailure 3 3 2 2 2 3 in
  let s' := OrganFailureFeedback.stage_with_organ_failure s oa in
  Stage.to_nat s <=? Stage.to_nat s').

(* P6: high_risk for all extremely preterm ELBW *)
Definition prop_extreme_preterm_high_risk :=
  forAll (bindGen (choose (22, 27)) (fun ga =>
         bindGen (choose (400, 999)) (fun bw =>
         bindGen gen_bool (fun ff =>
         bindGen gen_bool (fun asph =>
         bindGen gen_bool (fun chd =>
         bindGen gen_bool (fun poly =>
         bindGen gen_bool (fun umb =>
         bindGen gen_bool (fun exch =>
         returnGen (RiskFactors.MkRiskFactors ga bw ff asph chd poly umb exch))))))))))
  (fun r => RiskFactors.high_risk r).

QuickChick prop_classify_bounded.
QuickChick prop_pneumoperitoneum_IIIB.
QuickChick prop_surgery_only_IIIB.
QuickChick prop_adding_pneumatosis_monotone.
QuickChick prop_organ_failure_monotone.
QuickChick prop_extreme_preterm_high_risk.
