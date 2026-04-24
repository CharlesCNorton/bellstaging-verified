From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.

Import ListNotations.

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

(* Systemic level uses the same effective checks as classify_stage *)
Definition compute_systemic_level (c : ClinicalState.t) : nat :=
  let sys := ClinicalState.systemic c in
  let eff3 := SystemicSigns.stage3_signs sys
    || ClinicalState.effective_hypotension c
    || ClinicalState.has_dic c
    || ClinicalState.lab_neutropenia c in
  let eff2b := SystemicSigns.stage2b_signs sys
    || ClinicalState.lab_metabolic_acidosis c
    || ClinicalState.lab_thrombocytopenia c in
  if eff3 then 3
  else if eff2b then 2
  else if SystemicSigns.stage1_signs sys then 1
  else 0.

(* compute_systemic_level agrees with classify_stage's effective_stage3_sys:
   level >= 3 iff the same disjunction that classify_stage uses is true. *)
Lemma systemic_level_3_iff_effective_stage3 : forall c,
  let eff3 := SystemicSigns.stage3_signs (ClinicalState.systemic c)
    || ClinicalState.effective_hypotension c
    || ClinicalState.has_dic c
    || ClinicalState.lab_neutropenia c in
  (compute_systemic_level c >= 3) <-> (eff3 = true).
Proof.
  intros c. unfold compute_systemic_level. simpl.
  destruct (SystemicSigns.stage3_signs _ || _ || _ || _) eqn:E3.
  - split; intros; [reflexivity | lia].
  - split; intros H.
    + simpl in H. destruct (SystemicSigns.stage2b_signs _ || _ || _);
      simpl in H; try lia. destruct (SystemicSigns.stage1_signs _); simpl in H; lia.
    + discriminate.
Qed.

Lemma systemic_level_2_iff_effective_stage2b : forall c,
  let eff3 := SystemicSigns.stage3_signs (ClinicalState.systemic c)
    || ClinicalState.effective_hypotension c
    || ClinicalState.has_dic c
    || ClinicalState.lab_neutropenia c in
  let eff2b := SystemicSigns.stage2b_signs (ClinicalState.systemic c)
    || ClinicalState.lab_metabolic_acidosis c
    || ClinicalState.lab_thrombocytopenia c in
  (compute_systemic_level c >= 2) <-> (eff3 = true \/ eff2b = true).
Proof.
  intros c. unfold compute_systemic_level. simpl.
  destruct (SystemicSigns.stage3_signs _ || _ || _ || _) eqn:E3.
  - split; intros; [left; reflexivity | lia].
  - destruct (SystemicSigns.stage2b_signs _ || _ || _) eqn:E2b.
    + split; intros; [right; reflexivity | lia].
    + split; intros H.
      * destruct (SystemicSigns.stage1_signs _); simpl in H; lia.
      * destruct H; discriminate.
Qed.

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
  let sys_lv := compute_systemic_level c in
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
   classify_declarative uses threshold-based criteria matching;
   Classification.classify_stage uses specific sign combinations.
   Both share the same effective systemic level (lab/vitals-derived).

   The two classifiers encode genuinely different clinical interpretations
   at intermediate stages (IIA-IIB). classify_stage requires specific sign
   conjunctions per Bell; classify_declarative uses level thresholds.
   Full equivalence (forall c, classify c = classify_declarative c) does
   not hold by design — they are two valid readings of the staging criteria.

   Proved agreement:
   - IIIB: both fire on pneumoperitoneum (absolute indication)
   - Both bounded to [1,6]
   - Both deterministic and total

   Known divergences:
   - IIB: classify_stage requires intestinal_stage2_signs as separate
     conjunct; classify_declarative accepts intestinal_level >= 2 which
     includes stage2b_signs alone without stage2_signs
   - IIA: classify_stage requires definite_nec_findings (pneumatosis);
     classify_declarative requires systemic >= 1 + intestinal >= 2 +
     radiographic >= 2, which can fire on stage2a_findings without
     pneumatosis *)

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

(* Safety agreement: both classifiers agree on the surgical decision.
   If one says IIIB (surgery required), the other does too. *)
Theorem classify_agree_on_surgery : forall c,
  Classification.classify c = Stage.IIIB <-> classify_declarative c = Stage.IIIB.
Proof.
  intros c. split; intros H.
  - unfold Classification.classify, Classification.classify_stage in H.
    destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c)) eqn:Eperf.
    + apply classify_declarative_IIIB_on_perf. exact Eperf.
    + (* classify_stage only returns IIIB when pneumoperitoneum = true *)
      simpl in H.
      destruct ((_ && _ && _)%bool); try discriminate.
      destruct ((_ && _ && _)%bool); try discriminate.
      destruct ((_ && _)%bool); try discriminate.
      destruct ((_ && _)%bool); discriminate.
  - unfold classify_declarative in H.
    destruct (meets_criteria c stage_IIIB_criteria) eqn:Ecrit.
    + (* IIIB criteria met means radiographic_level >= 3, i.e. pneumoperitoneum *)
      unfold meets_criteria, stage_IIIB_criteria in Ecrit. simpl in Ecrit.
      unfold compute_radiographic_level in Ecrit.
      destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c)) eqn:Eperf.
      * apply Classification.pneumoperitoneum_forces_IIIB. exact Eperf.
      * (* radiographic_level < 3 when no pneumoperitoneum *)
        destruct (RadiographicSigns.stage2b_findings _); simpl in Ecrit; try discriminate.
        destruct (RadiographicSigns.definite_nec_findings _); simpl in Ecrit; try discriminate.
        destruct (RadiographicSigns.stage2a_findings _); simpl in Ecrit; try discriminate.
        destruct (RadiographicSigns.stage1_findings _); simpl in Ecrit; discriminate.
    + destruct (meets_criteria c stage_IIIA_criteria);
      destruct (meets_criteria c stage_IIB_criteria);
      destruct (meets_criteria c stage_IIA_criteria);
      destruct (meets_criteria c stage_IB_criteria); discriminate.
Qed.

(* Stage bounds are preserved *)
Lemma classify_declarative_bounded : forall c,
  1 <= Stage.to_nat (classify_declarative c) <= Stage.stage_count.
Proof.
  intros c. unfold classify_declarative, Stage.stage_count.
  destruct (meets_criteria c stage_IIIB_criteria);
  destruct (meets_criteria c stage_IIIA_criteria);
  destruct (meets_criteria c stage_IIB_criteria);
  destruct (meets_criteria c stage_IIA_criteria);
  destruct (meets_criteria c stage_IB_criteria);
  simpl; lia.
Qed.

(* ================================================================ *)
(* Exact disagreement characterization.                             *)
(*                                                                  *)
(* We construct concrete witness patients demonstrating divergence  *)
(* in each direction, prove the classification results by           *)
(* computation, and show full equivalence is refutable.             *)
(* ================================================================ *)

(* Minimal risk factors for clean witnesses *)
Definition divergence_risk : RiskFactors.t :=
  RiskFactors.MkRiskFactors 40 3500 false false false false false false.

(* --- Witness 1: declarative = IIB, procedural = IA --- *)
(* Systemic: metabolic_acidosis sign -> systemic_level = 2.
   Intestinal: abdominal_cellulitis only (stage2b, no stage2) -> int_level = 2.
   Radiographic: portal_venous_gas (stage2b finding) -> rad_level = 2.
   classify_declarative: sys >= 2, int >= 2, rad >= 2 -> IIB.
   classify_stage: IIB branch needs stage2_signs = true, but false -> falls to IA. *)
Definition wit_decl_IIB_proc_IA : ClinicalState.t :=
  ClinicalState.MkClinicalState
    divergence_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      false false false false true false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false false false true false false false)
    (RadiographicSigns.MkRadiographicSigns
      false false false false true false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma wit1_declarative : classify_declarative wit_decl_IIB_proc_IA = Stage.IIB.
Proof. vm_compute. reflexivity. Qed.

Lemma wit1_procedural : Classification.classify wit_decl_IIB_proc_IA = Stage.IA.
Proof. vm_compute. reflexivity. Qed.

(* --- Witness 2: declarative = IIA, procedural = IA --- *)
(* Systemic: temperature_instability -> systemic_level = 1.
   Intestinal: absent_bowel_sounds -> stage2_signs = true, int_level = 2.
   Radiographic: intestinal_dilation (stage2a, not pneumatosis) -> rad_level = 2.
   classify_declarative: sys >= 1, int >= 2, rad >= 2 -> IIA.
   classify_stage: IIA needs definite_nec_findings = pneumatosis = false -> IA. *)
Definition wit_decl_IIA_proc_IA : ClinicalState.t :=
  ClinicalState.MkClinicalState
    divergence_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      true false false false false false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false false false false false)
    (RadiographicSigns.MkRadiographicSigns
      false true false false false false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma wit2_declarative : classify_declarative wit_decl_IIA_proc_IA = Stage.IIA.
Proof. vm_compute. reflexivity. Qed.

Lemma wit2_procedural : Classification.classify wit_decl_IIA_proc_IA = Stage.IA.
Proof. vm_compute. reflexivity. Qed.

(* --- Witness 3: procedural = IIB, declarative = IA --- *)
(* Systemic: none -> systemic_level = 0.
   Intestinal: absent_bowel_sounds + cellulitis -> stage2 + stage2b, int_level = 2.
   Radiographic: portal_venous_gas -> stage2b, rad_level = 2.
   classify_stage: IIB = (false || true) && true && true -> IIB.
   classify_declarative: sys = 0 < 1 -> fails IB requirement -> IA. *)
Definition wit_proc_IIB_decl_IA : ClinicalState.t :=
  ClinicalState.MkClinicalState
    divergence_risk None None Microbiology.no_cultures None
    SystemicSigns.no_signs
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false true false false false)
    (RadiographicSigns.MkRadiographicSigns
      false false false false true false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma wit3_procedural : Classification.classify wit_proc_IIB_decl_IA = Stage.IIB.
Proof. vm_compute. reflexivity. Qed.

Lemma wit3_declarative : classify_declarative wit_proc_IIB_decl_IA = Stage.IA.
Proof. vm_compute. reflexivity. Qed.

(* --- Witness 4: procedural = IIA, declarative = IA --- *)
(* Systemic: none -> systemic_level = 0.
   Intestinal: absent_bowel_sounds -> stage2 = true, int_level = 2.
   Radiographic: pneumatosis -> definite_nec, rad_level = 2.
   classify_stage: IIA = pneumatosis && stage2 = true -> IIA.
   classify_declarative: sys = 0 < 1 -> IA. *)
Definition wit_proc_IIA_decl_IA : ClinicalState.t :=
  ClinicalState.MkClinicalState
    divergence_risk None None Microbiology.no_cultures None
    SystemicSigns.no_signs
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false false false false false)
    (RadiographicSigns.MkRadiographicSigns
      false false false true false false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma wit4_procedural : Classification.classify wit_proc_IIA_decl_IA = Stage.IIA.
Proof. vm_compute. reflexivity. Qed.

Lemma wit4_declarative : classify_declarative wit_proc_IIA_decl_IA = Stage.IA.
Proof. vm_compute. reflexivity. Qed.

(* The two classifiers are not equivalent. *)
Theorem classifiers_not_equivalent
  : ~ (forall c, Classification.classify c = classify_declarative c).
Proof.
  intro H.
  pose proof (H wit_decl_IIB_proc_IA) as Hw.
  rewrite wit1_procedural in Hw. rewrite wit1_declarative in Hw.
  discriminate.
Qed.

(* Divergence is bidirectional: neither classifier uniformly dominates. *)
Theorem divergence_bidirectional
  : (exists c, Stage.to_nat (classify_declarative c)
               > Stage.to_nat (Classification.classify c))
    /\ (exists c, Stage.to_nat (Classification.classify c)
                  > Stage.to_nat (classify_declarative c)).
Proof.
  split.
  - exists wit_decl_IIB_proc_IA.
    rewrite wit1_declarative, wit1_procedural. simpl. lia.
  - exists wit_proc_IIB_decl_IA.
    rewrite wit3_procedural, wit3_declarative. simpl. lia.
Qed.

(* Maximum observed gap: 3 ordinal stages (IIB vs IA). *)
Lemma max_divergence_decl_higher
  : Stage.to_nat (classify_declarative wit_decl_IIB_proc_IA)
    - Stage.to_nat (Classification.classify wit_decl_IIB_proc_IA) = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma max_divergence_proc_higher
  : Stage.to_nat (Classification.classify wit_proc_IIB_decl_IA)
    - Stage.to_nat (classify_declarative wit_proc_IIB_decl_IA) = 3.
Proof. vm_compute. reflexivity. Qed.

(* Despite intermediate disagreement, both agree on the surgical
   boundary (IIIB). See classify_agree_on_surgery above. *)

(* Surjectivity witnesses for classify_declarative: one concrete state
   per stage. *)

Definition decl_risk : RiskFactors.t := divergence_risk.

(* IA: no findings of any kind *)
Definition decl_IA_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    SystemicSigns.no_signs IntestinalSigns.no_signs
    RadiographicSigns.no_findings
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IA_stages : classify_declarative decl_IA_state = Stage.IA.
Proof. vm_compute. reflexivity. Qed.

(* IB: systemic stage1 + intestinal gross-blood *)
Definition decl_IB_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      true false false false false false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false true false false false false false false)
    RadiographicSigns.no_findings
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IB_stages : classify_declarative decl_IB_state = Stage.IB.
Proof. vm_compute. reflexivity. Qed.

(* IIA: systemic >= 1, intestinal >= 2 (stage2), radiographic >= 2 (stage2a) *)
Definition decl_IIA_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      true false false false false false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false false false false false)
    (RadiographicSigns.MkRadiographicSigns
      false true false false false false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IIA_stages : classify_declarative decl_IIA_state = Stage.IIA.
Proof. vm_compute. reflexivity. Qed.

(* IIB: systemic >= 2 (metabolic acidosis) + intestinal >= 2 + rad >= 2 (stage2b) *)
Definition decl_IIB_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      false false false false true false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false false false false false)
    (RadiographicSigns.MkRadiographicSigns
      false false false false true false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IIB_stages : classify_declarative decl_IIB_state = Stage.IIB.
Proof. vm_compute. reflexivity. Qed.

(* IIIA: systemic >= 3 (hypotension) + intestinal >= 3 + rad >= 2 (stage2b) *)
Definition decl_IIIA_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      false false false false false false true false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false false false false false true false)
    (RadiographicSigns.MkRadiographicSigns
      false false false false true false false)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IIIA_stages : classify_declarative decl_IIIA_state = Stage.IIIA.
Proof. vm_compute. reflexivity. Qed.

(* IIIB: pneumoperitoneum *)
Definition decl_IIIB_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    SystemicSigns.no_signs IntestinalSigns.no_signs
    (RadiographicSigns.MkRadiographicSigns
      false false false false false false true)
    NeonatalOrganFailure.NeuroNormal 0 0 0 0.

Lemma decl_IIIB_stages : classify_declarative decl_IIIB_state = Stage.IIIB.
Proof. vm_compute. reflexivity. Qed.

Theorem classify_declarative_surjective : forall s : Stage.t,
  exists c : ClinicalState.t, classify_declarative c = s.
Proof.
  intros []; eexists;
  [ exact decl_IA_stages
  | exact decl_IB_stages
  | exact decl_IIA_stages
  | exact decl_IIB_stages
  | exact decl_IIIA_stages
  | exact decl_IIIB_stages ].
Qed.

End BellCriteria.
