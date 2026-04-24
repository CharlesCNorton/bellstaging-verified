From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.

Import ListNotations.
Open Scope string_scope.

Module Serialization.

(* Tree-shaped value type used as the serialization target. Supports both
   positional JList encoding (for roundtrip proofs) and keyed JObject
   encoding (for FHIR-compatible JSON emission). *)

Inductive JValue : Type :=
  | JNull : JValue
  | JBool : bool -> JValue
  | JNat : nat -> JValue
  | JStr : string -> JValue
  | JList : list JValue -> JValue
  | JObject : list (string * JValue) -> JValue.

(* --- Small enum and option helpers --- *)

Definition ser_culture (c : Microbiology.CultureStatus) : JValue :=
  match c with
  | Microbiology.NotCollected => JNat 0
  | Microbiology.Pending => JNat 1
  | Microbiology.Negative => JNat 2
  | Microbiology.PositiveGramNeg => JNat 3
  | Microbiology.PositiveGramPos => JNat 4
  | Microbiology.PositiveFungal => JNat 5
  end.

Definition deser_culture (j : JValue) : option Microbiology.CultureStatus :=
  match j with
  | JNat 0 => Some Microbiology.NotCollected
  | JNat 1 => Some Microbiology.Pending
  | JNat 2 => Some Microbiology.Negative
  | JNat 3 => Some Microbiology.PositiveGramNeg
  | JNat 4 => Some Microbiology.PositiveGramPos
  | JNat 5 => Some Microbiology.PositiveFungal
  | _ => None
  end.

Lemma culture_roundtrip : forall c, deser_culture (ser_culture c) = Some c.
Proof. destruct c; reflexivity. Qed.

Definition ser_neuro (n : NeonatalOrganFailure.NeuroStatus) : JValue :=
  match n with
  | NeonatalOrganFailure.NeuroNormal => JNat 0
  | NeonatalOrganFailure.SarnatI => JNat 1
  | NeonatalOrganFailure.SarnatII => JNat 2
  | NeonatalOrganFailure.SarnatIII => JNat 3
  end.

Definition deser_neuro (j : JValue) : option NeonatalOrganFailure.NeuroStatus :=
  match j with
  | JNat 0 => Some NeonatalOrganFailure.NeuroNormal
  | JNat 1 => Some NeonatalOrganFailure.SarnatI
  | JNat 2 => Some NeonatalOrganFailure.SarnatII
  | JNat 3 => Some NeonatalOrganFailure.SarnatIII
  | _ => None
  end.

Lemma neuro_roundtrip : forall n, deser_neuro (ser_neuro n) = Some n.
Proof. destruct n; reflexivity. Qed.

Definition ser_opt_nat (o : option nat) : JValue :=
  match o with
  | Some n => JList [JNat 1; JNat n]
  | None => JList [JNat 0]
  end.

Definition deser_opt_nat (j : JValue) : option (option nat) :=
  match j with
  | JList [JNat 0] => Some None
  | JList [JNat 1; JNat n] => Some (Some n)
  | _ => None
  end.

Lemma opt_nat_roundtrip : forall o, deser_opt_nat (ser_opt_nat o) = Some o.
Proof. destruct o; reflexivity. Qed.

(* --- Per-record serializers --- *)

Definition ser_rf (r : RiskFactors.t) : JValue :=
  JList [JNat (RiskFactors.gestational_age_weeks r);
         JNat (RiskFactors.birth_weight_grams r);
         JBool (RiskFactors.formula_fed r);
         JBool (RiskFactors.history_of_perinatal_asphyxia r);
         JBool (RiskFactors.congenital_heart_disease r);
         JBool (RiskFactors.polycythemia r);
         JBool (RiskFactors.umbilical_catheter r);
         JBool (RiskFactors.exchange_transfusion r)].

Definition deser_rf (j : JValue) : option RiskFactors.t :=
  match j with
  | JList [JNat ga; JNat bw; JBool ff; JBool asph;
           JBool chd; JBool poly; JBool umb; JBool exch] =>
      Some (RiskFactors.MkRiskFactors ga bw ff asph chd poly umb exch)
  | _ => None
  end.

Lemma rf_roundtrip : forall r, deser_rf (ser_rf r) = Some r.
Proof. destruct r; reflexivity. Qed.

Definition ser_labs (l : LabValues.t) : JValue :=
  JList [JNat (LabValues.wbc_k_per_uL l);
         JNat (LabValues.absolute_neutrophil_count l);
         JNat (LabValues.platelet_k_per_uL l);
         JNat (LabValues.crp_mg_L l);
         JNat (LabValues.procalcitonin_ng_mL_x10 l);
         JNat (LabValues.lactate_mmol_L_x10 l);
         JNat (LabValues.ph_x100 l);
         JNat (LabValues.base_deficit l);
         JNat (LabValues.pco2_mmHg l);
         JNat (LabValues.glucose_mg_dL l)].

Definition deser_labs (j : JValue) : option LabValues.t :=
  match j with
  | JList [JNat wbc; JNat anc; JNat plt; JNat crp; JNat pct;
           JNat lac; JNat ph; JNat bd; JNat pco2; JNat glu] =>
      Some (LabValues.MkLabValues wbc anc plt crp pct lac ph bd pco2 glu)
  | _ => None
  end.

Lemma labs_roundtrip : forall l, deser_labs (ser_labs l) = Some l.
Proof. destruct l; reflexivity. Qed.

Definition ser_coag (c : CoagulationPanel.t) : JValue :=
  JList [JNat (CoagulationPanel.pt_seconds_x10 c);
         JNat (CoagulationPanel.inr_x100 c);
         JNat (CoagulationPanel.fibrinogen_mg_dL c);
         JNat (CoagulationPanel.ionized_calcium_x100 c)].

Definition deser_coag (j : JValue) : option CoagulationPanel.t :=
  match j with
  | JList [JNat pt; JNat inr_; JNat fib; JNat ica] =>
      Some (CoagulationPanel.MkCoagPanel pt inr_ fib ica)
  | _ => None
  end.

Lemma coag_roundtrip : forall c, deser_coag (ser_coag c) = Some c.
Proof. destruct c; reflexivity. Qed.

Definition ser_micro (m : Microbiology.t) : JValue :=
  JList [ser_culture (Microbiology.blood_culture m);
         ser_opt_nat (Microbiology.blood_culture_collected_h m);
         ser_opt_nat (Microbiology.blood_culture_resulted_h m);
         ser_culture (Microbiology.csf_culture m);
         ser_opt_nat (Microbiology.csf_culture_collected_h m);
         ser_opt_nat (Microbiology.csf_culture_resulted_h m);
         ser_culture (Microbiology.peritoneal_culture m);
         ser_opt_nat (Microbiology.peritoneal_culture_collected_h m);
         ser_opt_nat (Microbiology.peritoneal_culture_resulted_h m)].

Definition deser_micro (j : JValue) : option Microbiology.t :=
  match j with
  | JList [bc; bcc; bcr; csfc; csfcc; csfcr; pc; pcc; pcr] =>
      match deser_culture bc, deser_opt_nat bcc, deser_opt_nat bcr,
            deser_culture csfc, deser_opt_nat csfcc, deser_opt_nat csfcr,
            deser_culture pc, deser_opt_nat pcc, deser_opt_nat pcr with
      | Some bc', Some bcc', Some bcr',
        Some csfc', Some csfcc', Some csfcr',
        Some pc', Some pcc', Some pcr' =>
          Some (Microbiology.MkMicrobiology
                  bc' bcc' bcr' csfc' csfcc' csfcr' pc' pcc' pcr')
      | _, _, _, _, _, _, _, _, _ => None
      end
  | _ => None
  end.

Lemma micro_roundtrip : forall m, deser_micro (ser_micro m) = Some m.
Proof.
  destruct m. simpl.
  rewrite !culture_roundtrip, !opt_nat_roundtrip.
  reflexivity.
Qed.

Definition ser_vitals (v : VitalSigns.t) : JValue :=
  JList [JNat (VitalSigns.heart_rate_bpm v);
         JNat (VitalSigns.respiratory_rate_bpm v);
         JNat (VitalSigns.temperature_x10 v);
         JNat (VitalSigns.systolic_bp_mmHg v);
         JNat (VitalSigns.diastolic_bp_mmHg v);
         JNat (VitalSigns.map_mmHg v);
         JNat (VitalSigns.spo2_percent v)].

Definition deser_vitals (j : JValue) : option VitalSigns.t :=
  match j with
  | JList [JNat hr; JNat rr; JNat temp; JNat sbp; JNat dbp; JNat map; JNat spo2] =>
      Some (VitalSigns.MkVitalSigns hr rr temp sbp dbp map spo2)
  | _ => None
  end.

Lemma vitals_roundtrip : forall v, deser_vitals (ser_vitals v) = Some v.
Proof. destruct v; reflexivity. Qed.

Definition ser_sys (s : SystemicSigns.t) : JValue :=
  JList [JBool (SystemicSigns.temperature_instability s);
         JBool (SystemicSigns.apnea s);
         JBool (SystemicSigns.bradycardia s);
         JBool (SystemicSigns.lethargy s);
         JBool (SystemicSigns.metabolic_acidosis s);
         JBool (SystemicSigns.thrombocytopenia s);
         JBool (SystemicSigns.hypotension s);
         JBool (SystemicSigns.respiratory_failure s);
         JBool (SystemicSigns.dic s);
         JBool (SystemicSigns.neutropenia s)].

Definition deser_sys (j : JValue) : option SystemicSigns.t :=
  match j with
  | JList [JBool ti; JBool ap; JBool br; JBool le; JBool ma;
           JBool th; JBool hy; JBool rf; JBool di; JBool ne] =>
      Some (SystemicSigns.MkSystemicSigns ti ap br le ma th hy rf di ne)
  | _ => None
  end.

Lemma sys_roundtrip : forall s, deser_sys (ser_sys s) = Some s.
Proof. destruct s; reflexivity. Qed.

Definition ser_int (i : IntestinalSigns.t) : JValue :=
  JList [JBool (IntestinalSigns.elevated_gastric_residuals i);
         JBool (IntestinalSigns.mild_abdominal_distension i);
         JBool (IntestinalSigns.occult_blood_in_stool i);
         JBool (IntestinalSigns.gross_blood_in_stool i);
         JBool (IntestinalSigns.absent_bowel_sounds i);
         JBool (IntestinalSigns.abdominal_tenderness i);
         JBool (IntestinalSigns.abdominal_cellulitis i);
         JBool (IntestinalSigns.right_lower_quadrant_mass i);
         JBool (IntestinalSigns.marked_distension i);
         JBool (IntestinalSigns.peritonitis i)].

Definition deser_int (j : JValue) : option IntestinalSigns.t :=
  match j with
  | JList [JBool egr; JBool mad; JBool obs; JBool gbs; JBool abs_;
           JBool at_; JBool ac; JBool rlq; JBool md; JBool per] =>
      Some (IntestinalSigns.MkIntestinalSigns egr mad obs gbs abs_ at_ ac rlq md per)
  | _ => None
  end.

Lemma int_roundtrip : forall i, deser_int (ser_int i) = Some i.
Proof. destruct i; reflexivity. Qed.

Definition ser_rad (r : RadiographicSigns.t) : JValue :=
  JList [JBool (RadiographicSigns.normal_or_mild_ileus r);
         JBool (RadiographicSigns.intestinal_dilation r);
         JBool (RadiographicSigns.focal_ileus r);
         JBool (RadiographicSigns.pneumatosis_intestinalis r);
         JBool (RadiographicSigns.portal_venous_gas r);
         JBool (RadiographicSigns.ascites r);
         JBool (RadiographicSigns.pneumoperitoneum r)].

Definition deser_rad (j : JValue) : option RadiographicSigns.t :=
  match j with
  | JList [JBool nmi; JBool id_; JBool fi; JBool pi_;
           JBool pvg; JBool asc; JBool pnp] =>
      Some (RadiographicSigns.MkRadiographicSigns nmi id_ fi pi_ pvg asc pnp)
  | _ => None
  end.

Lemma rad_roundtrip : forall r, deser_rad (ser_rad r) = Some r.
Proof. destruct r; reflexivity. Qed.

(* Option wrapper for labs/coag/vitals *)
Definition ser_opt {A : Type} (ser : A -> JValue) (o : option A) : JValue :=
  match o with
  | Some a => JList [JNat 1; ser a]
  | None => JList [JNat 0]
  end.

Definition deser_opt {A : Type} (deser : JValue -> option A) (j : JValue)
  : option (option A) :=
  match j with
  | JList [JNat 0] => Some None
  | JList [JNat 1; v] =>
      match deser v with
      | Some a => Some (Some a)
      | None => None
      end
  | _ => None
  end.

Lemma opt_roundtrip : forall {A : Type} (ser : A -> JValue) (deser : JValue -> option A) (o : option A),
  (forall a, deser (ser a) = Some a) ->
  deser_opt deser (ser_opt ser o) = Some o.
Proof.
  intros A ser deser o Hrt. destruct o; simpl.
  - rewrite Hrt. reflexivity.
  - reflexivity.
Qed.

(* --- ClinicalState serializer --- *)

Definition ser_cs (c : ClinicalState.t) : JValue :=
  JList [ser_rf (ClinicalState.risk_factors c);
         ser_opt ser_labs (ClinicalState.labs c);
         ser_opt ser_coag (ClinicalState.coag c);
         ser_micro (ClinicalState.micro c);
         ser_opt ser_vitals (ClinicalState.vitals c);
         ser_sys (ClinicalState.systemic c);
         ser_int (ClinicalState.intestinal c);
         ser_rad (ClinicalState.radiographic c);
         ser_neuro (ClinicalState.neuro_status c);
         JNat (ClinicalState.hours_since_symptom_onset c);
         JNat (ClinicalState.systemic_assessed_h c);
         JNat (ClinicalState.intestinal_assessed_h c);
         JNat (ClinicalState.radiographic_assessed_h c)].

Definition deser_cs (j : JValue) : option ClinicalState.t :=
  match j with
  | JList [jrf; jlabs; jcoag; jmicro; jvitals; jsys; jint; jrad; jneuro;
           JNat hso; JNat sah; JNat iah; JNat rah] =>
      match deser_rf jrf,
            deser_opt deser_labs jlabs,
            deser_opt deser_coag jcoag,
            deser_micro jmicro,
            deser_opt deser_vitals jvitals,
            deser_sys jsys,
            deser_int jint,
            deser_rad jrad,
            deser_neuro jneuro with
      | Some rf, Some labs, Some coag, Some micro,
        Some vitals, Some sys, Some int, Some rad, Some neuro =>
          Some (ClinicalState.MkClinicalState
                  rf labs coag micro vitals sys int rad neuro
                  hso sah iah rah)
      | _, _, _, _, _, _, _, _, _ => None
      end
  | _ => None
  end.

Theorem cs_roundtrip : forall c, deser_cs (ser_cs c) = Some c.
Proof.
  intros c. destruct c as [rf labs coag micro vitals sys int rad neuro hso sah iah rah].
  unfold ser_cs, deser_cs.
  rewrite rf_roundtrip.
  rewrite (opt_roundtrip ser_labs deser_labs _ labs_roundtrip).
  rewrite (opt_roundtrip ser_coag deser_coag _ coag_roundtrip).
  rewrite micro_roundtrip.
  rewrite (opt_roundtrip ser_vitals deser_vitals _ vitals_roundtrip).
  rewrite sys_roundtrip.
  rewrite int_roundtrip.
  rewrite rad_roundtrip.
  rewrite neuro_roundtrip.
  reflexivity.
Qed.

(* --- Classifier gate through the serializer --- *)

Definition ser_stage (s : Stage.t) : JValue := JNat (Stage.to_nat s).

Definition classify_serialized (j : JValue) : option JValue :=
  match deser_cs j with
  | Some c => Some (ser_stage (Classification.classify c))
  | None => None
  end.

Theorem classify_serialized_agrees : forall c,
  classify_serialized (ser_cs c) = Some (ser_stage (Classification.classify c)).
Proof.
  intros c. unfold classify_serialized.
  rewrite cs_roundtrip. reflexivity.
Qed.

(* --- FHIR-keyed serialization ---
   Emits each ClinicalState field as a named entry in a JObject.
   Intended for JSON rendering downstream (OCaml / Python library
   converts JObject to FHIR Bundle shape). The outer keys map to
   FHIR resource types (Patient, Observation, Condition). *)

Definition kv_nat (key : string) (n : nat) : string * JValue :=
  (key, JNat n).

Definition kv_bool (key : string) (b : bool) : string * JValue :=
  (key, JBool b).

Definition kv_str (key : string) (s : string) : string * JValue :=
  (key, JStr s).

Definition rf_fields (r : RiskFactors.t) : list (string * JValue) :=
  [kv_nat "gestationalAgeWeeks" (RiskFactors.gestational_age_weeks r);
   kv_nat "birthWeightGrams" (RiskFactors.birth_weight_grams r);
   kv_bool "formulaFed" (RiskFactors.formula_fed r);
   kv_bool "perinatalAsphyxia" (RiskFactors.history_of_perinatal_asphyxia r);
   kv_bool "congenitalHeartDisease" (RiskFactors.congenital_heart_disease r);
   kv_bool "polycythemia" (RiskFactors.polycythemia r);
   kv_bool "umbilicalCatheter" (RiskFactors.umbilical_catheter r);
   kv_bool "exchangeTransfusion" (RiskFactors.exchange_transfusion r)].

Definition labs_fields (l : LabValues.t) : list (string * JValue) :=
  [kv_nat "wbcKPerUL" (LabValues.wbc_k_per_uL l);
   kv_nat "absoluteNeutrophilCount" (LabValues.absolute_neutrophil_count l);
   kv_nat "plateletKPerUL" (LabValues.platelet_k_per_uL l);
   kv_nat "crpMgL" (LabValues.crp_mg_L l);
   kv_nat "procalcitoninNgMLx10" (LabValues.procalcitonin_ng_mL_x10 l);
   kv_nat "lactateMmolLx10" (LabValues.lactate_mmol_L_x10 l);
   kv_nat "phX100" (LabValues.ph_x100 l);
   kv_nat "baseDeficit" (LabValues.base_deficit l);
   kv_nat "pco2MmHg" (LabValues.pco2_mmHg l);
   kv_nat "glucoseMgDL" (LabValues.glucose_mg_dL l)].

Definition systemic_fields (s : SystemicSigns.t) : list (string * JValue) :=
  [kv_bool "temperatureInstability" (SystemicSigns.temperature_instability s);
   kv_bool "apnea" (SystemicSigns.apnea s);
   kv_bool "bradycardia" (SystemicSigns.bradycardia s);
   kv_bool "lethargy" (SystemicSigns.lethargy s);
   kv_bool "metabolicAcidosis" (SystemicSigns.metabolic_acidosis s);
   kv_bool "thrombocytopenia" (SystemicSigns.thrombocytopenia s);
   kv_bool "hypotension" (SystemicSigns.hypotension s);
   kv_bool "respiratoryFailure" (SystemicSigns.respiratory_failure s);
   kv_bool "dic" (SystemicSigns.dic s);
   kv_bool "neutropenia" (SystemicSigns.neutropenia s)].

Definition intestinal_fields (i : IntestinalSigns.t) : list (string * JValue) :=
  [kv_bool "elevatedGastricResiduals" (IntestinalSigns.elevated_gastric_residuals i);
   kv_bool "mildAbdominalDistension" (IntestinalSigns.mild_abdominal_distension i);
   kv_bool "occultBloodInStool" (IntestinalSigns.occult_blood_in_stool i);
   kv_bool "grossBloodInStool" (IntestinalSigns.gross_blood_in_stool i);
   kv_bool "absentBowelSounds" (IntestinalSigns.absent_bowel_sounds i);
   kv_bool "abdominalTenderness" (IntestinalSigns.abdominal_tenderness i);
   kv_bool "abdominalCellulitis" (IntestinalSigns.abdominal_cellulitis i);
   kv_bool "rightLowerQuadrantMass" (IntestinalSigns.right_lower_quadrant_mass i);
   kv_bool "markedDistension" (IntestinalSigns.marked_distension i);
   kv_bool "peritonitis" (IntestinalSigns.peritonitis i)].

Definition radiographic_fields (r : RadiographicSigns.t) : list (string * JValue) :=
  [kv_bool "normalOrMildIleus" (RadiographicSigns.normal_or_mild_ileus r);
   kv_bool "intestinalDilation" (RadiographicSigns.intestinal_dilation r);
   kv_bool "focalIleus" (RadiographicSigns.focal_ileus r);
   kv_bool "pneumatosisIntestinalis" (RadiographicSigns.pneumatosis_intestinalis r);
   kv_bool "portalVenousGas" (RadiographicSigns.portal_venous_gas r);
   kv_bool "ascites" (RadiographicSigns.ascites r);
   kv_bool "pneumoperitoneum" (RadiographicSigns.pneumoperitoneum r)].

Definition neuro_string (n : NeonatalOrganFailure.NeuroStatus) : string :=
  match n with
  | NeonatalOrganFailure.NeuroNormal => "NeuroNormal"
  | NeonatalOrganFailure.SarnatI => "SarnatI"
  | NeonatalOrganFailure.SarnatII => "SarnatII"
  | NeonatalOrganFailure.SarnatIII => "SarnatIII"
  end.

Definition stage_string (s : Stage.t) : string :=
  match s with
  | Stage.IA => "IA"
  | Stage.IB => "IB"
  | Stage.IIA => "IIA"
  | Stage.IIB => "IIB"
  | Stage.IIIA => "IIIA"
  | Stage.IIIB => "IIIB"
  end.

(* FHIR-shaped Bundle: groups keyed fields under resource-type names. *)
Definition ser_cs_fhir (c : ClinicalState.t) : JValue :=
  JObject
    [("resourceType", JStr "Bundle");
     ("type", JStr "collection");
     ("patient", JObject
        (("resourceType", JStr "Patient") :: rf_fields (ClinicalState.risk_factors c)));
     ("observationLabs",
        match ClinicalState.labs c with
        | Some l => JObject (("resourceType", JStr "Observation") :: labs_fields l)
        | None => JNull
        end);
     ("observationSystemic", JObject
        (("resourceType", JStr "Observation") ::
         systemic_fields (ClinicalState.systemic c)));
     ("observationIntestinal", JObject
        (("resourceType", JStr "Observation") ::
         intestinal_fields (ClinicalState.intestinal c)));
     ("observationRadiographic", JObject
        (("resourceType", JStr "DiagnosticReport") ::
         radiographic_fields (ClinicalState.radiographic c)));
     ("neuroStatus", JStr (neuro_string (ClinicalState.neuro_status c)));
     ("hoursSinceSymptomOnset", JNat (ClinicalState.hours_since_symptom_onset c))].

Definition ser_stage_fhir (s : Stage.t) : JValue :=
  JObject
    [("resourceType", JStr "Condition");
     ("code", JStr "NEC");
     ("stage", JStr (stage_string s));
     ("stageNumeric", JNat (Stage.to_nat s))].

(* Classification via FHIR-shaped input yields a FHIR Condition. *)
Definition classify_fhir (c : ClinicalState.t) : JValue :=
  ser_stage_fhir (Classification.classify c).

Lemma neuro_string_injective : forall n1 n2,
  neuro_string n1 = neuro_string n2 -> n1 = n2.
Proof. intros [] []; simpl; intros H; try reflexivity; discriminate. Qed.

Lemma stage_string_injective : forall s1 s2,
  stage_string s1 = stage_string s2 -> s1 = s2.
Proof. intros [] []; simpl; intros H; try reflexivity; discriminate. Qed.

Lemma ser_stage_fhir_agrees : forall s,
  ser_stage_fhir s =
  JObject [("resourceType", JStr "Condition");
           ("code", JStr "NEC");
           ("stage", JStr (stage_string s));
           ("stageNumeric", JNat (Stage.to_nat s))].
Proof. reflexivity. Qed.

End Serialization.
