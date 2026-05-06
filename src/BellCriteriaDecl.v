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

(* Radiographic level encoding refined to distinguish specificity:
   Level 3 (pneumoperitoneum) — absolute surgical indication.
   Level 2 (PVG, ascites, pneumatosis) — Bell-pathognomonic NEC findings.
   Level 1 (intestinal dilation, focal ileus, mild ileus) — nonspecific.
   Level 0 — no findings.
   The earlier encoding collapsed stage2a_findings (intestinal dilation
   alone) into level 2, which let the declarative classifier reach IIA
   on a finding that the procedural classifier (Bell-faithful) rejects.
   This change closes the wit_decl_IIA_proc_IA divergence (now IB vs IA,
   gap 1) without changing IIIB safety — pneumoperitoneum still maps to 3. *)
Definition compute_radiographic_level (r : RadiographicSigns.t) : nat :=
  if RadiographicSigns.pneumoperitoneum r then 3
  else if RadiographicSigns.stage2b_findings r then 2
  else if RadiographicSigns.definite_nec_findings r then 2
  else if RadiographicSigns.stage2a_findings r then 1
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

   Known divergences (after the radiographic-level refinement):
   - IIB: classify_stage requires intestinal_stage2_signs as a separate
     conjunct; classify_declarative accepts intestinal_level >= 2 which
     includes stage2b_signs alone without stage2_signs.
   - IIA from PVG-only: PVG triggers radiographic_level >= 2, allowing
     declarative IIA when systemic and intestinal levels are met without
     pneumatosis (which the procedural classifier requires).
   The narrower divergence "IIA from intestinal_dilation alone" is now
   closed by compute_radiographic_level — stage2a_findings without
   pneumatosis maps to level 1, not 2. *)

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

(* --- Witness 2: declarative = IB, procedural = IA --- *)
(* Systemic: temperature_instability -> systemic_level = 1.
   Intestinal: absent_bowel_sounds -> stage2_signs = true, int_level = 2.
   Radiographic: intestinal_dilation only (stage2a, not pneumatosis).
   Under the refined compute_radiographic_level, stage2a_findings
   without pneumatosis maps to rad_level = 1, not 2.
   classify_declarative: sys >= 1, int >= 1 met for IB; IIA fails on rad < 2
     -> IB.
   classify_stage: IIA needs definite_nec_findings = pneumatosis = false;
     IB needs gross_blood_in_stool = false -> falls through to IA.
   The earlier "declarative=IIA, procedural=IA" divergence (gap 2) is
   reduced to "declarative=IB, procedural=IA" (gap 1) by the refinement. *)
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

Lemma wit2_declarative : classify_declarative wit_decl_IIA_proc_IA = Stage.IB.
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

(* IIA: systemic >= 1, intestinal >= 2 (stage2), radiographic >= 2.
   Uses pneumatosis_intestinalis to reach rad_level = 2 under the
   refined compute_radiographic_level (stage2a_findings alone is now
   level 1). *)
Definition decl_IIA_state : ClinicalState.t :=
  ClinicalState.MkClinicalState
    decl_risk None None Microbiology.no_cultures None
    (SystemicSigns.MkSystemicSigns
      true false false false false false false false false false)
    (IntestinalSigns.MkIntestinalSigns
      false false false false true false false false false false)
    (RadiographicSigns.MkRadiographicSigns
      false false false true false false false)
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

(* Validity proofs for the divergence and surjectivity witnesses.
   All use divergence_risk (GA 40, BW 3500), which falls outside both
   the extreme-prematurity-with-macrosomia and post-term-with-ELBW
   exclusions of the tightened valid predicate. Labs and vitals are
   None, satisfying the option-None branches vacuously. *)
Lemma wit_decl_IIB_proc_IA_valid : ClinicalState.valid wit_decl_IIB_proc_IA.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma wit_decl_IIA_proc_IA_valid : ClinicalState.valid wit_decl_IIA_proc_IA.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma wit_proc_IIB_decl_IA_valid : ClinicalState.valid wit_proc_IIB_decl_IA.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma wit_proc_IIA_decl_IA_valid : ClinicalState.valid wit_proc_IIA_decl_IA.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IA_state_valid : ClinicalState.valid decl_IA_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IB_state_valid : ClinicalState.valid decl_IB_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IIA_state_valid : ClinicalState.valid decl_IIA_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IIB_state_valid : ClinicalState.valid decl_IIB_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IIIA_state_valid : ClinicalState.valid decl_IIIA_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

Lemma decl_IIIB_state_valid : ClinicalState.valid decl_IIIB_state.
Proof. apply ClinicalState.is_valid_iff. vm_compute. reflexivity. Qed.

(* Helper: extract the radiographic-level requirement from a declarative
   IIA verdict. The simpl tactic reduces (2 <=? n) into match-on-n form,
   so we destruct the level value to discharge the case analysis.
   The IIA-criterion fact is established via assert/case-analysis to
   avoid `destruct ... eqn:` which trips a primitive-equality error
   on the boolean returned by meets_criteria under Rocq 9. *)
Lemma classify_declarative_IIA_requires_rad_level_2 : forall c,
  classify_declarative c = Stage.IIA ->
  2 <= compute_radiographic_level (ClinicalState.radiographic c).
Proof.
  intros c H.
  assert (E_IIA : meets_criteria c stage_IIA_criteria = true).
  { unfold classify_declarative in H.
    destruct (meets_criteria c stage_IIIB_criteria); [discriminate|].
    destruct (meets_criteria c stage_IIIA_criteria); [discriminate|].
    destruct (meets_criteria c stage_IIB_criteria); [discriminate|].
    destruct (meets_criteria c stage_IIA_criteria); [reflexivity|].
    destruct (meets_criteria c stage_IB_criteria); discriminate. }
  unfold meets_criteria, stage_IIA_criteria in E_IIA.
  apply andb_true_iff in E_IIA. destruct E_IIA as [_ E_rad].
  simpl in E_rad.
  destruct (compute_radiographic_level (ClinicalState.radiographic c))
    as [|[|n]]; [discriminate | discriminate | lia].
Qed.

(* ================================================================ *)
(* Consensus classifier: returns Some s only when both procedural   *)
(* and declarative classifiers agree. Disagreement (the principled  *)
(* PVG-without-pneumatosis case, plus a small enumerable residual)  *)
(* yields None, surfacing the divergence to the caller rather than  *)
(* picking one reading silently.                                    *)
(* ================================================================ *)

Definition stage_eqb (s1 s2 : Stage.t) : bool :=
  Stage.to_nat s1 =? Stage.to_nat s2.

Lemma stage_eqb_refl : forall s, stage_eqb s s = true.
Proof. intro s. unfold stage_eqb. apply Nat.eqb_refl. Qed.

Lemma stage_eqb_eq : forall s1 s2, stage_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros [] []; split; intro H; vm_compute in H;
  try reflexivity; try discriminate; vm_compute; reflexivity.
Qed.

Definition classify_consensus (c : ClinicalState.t) : option Stage.t :=
  let s_proc := Classification.classify c in
  let s_decl := classify_declarative c in
  if stage_eqb s_proc s_decl then Some s_proc else None.

(* The consensus classifier returns Some iff both classifiers agree;
   the returned stage equals each of them. *)
Lemma consensus_some_iff : forall c s,
  classify_consensus c = Some s <->
  Classification.classify c = s /\ classify_declarative c = s.
Proof.
  intros c s. split.
  - intro H. unfold classify_consensus in H.
    destruct (stage_eqb (Classification.classify c) (classify_declarative c)) eqn:E;
      [|discriminate].
    apply stage_eqb_eq in E.
    injection H as Hs. split; [exact Hs | rewrite <- Hs; symmetry; exact E].
  - intros [Hp Hd]. unfold classify_consensus.
    rewrite Hp, Hd, stage_eqb_refl. reflexivity.
Qed.

(* The consensus classifier returns None iff the two classifiers disagree. *)
Lemma consensus_none_iff_disagree : forall c,
  classify_consensus c = None <->
  Classification.classify c <> classify_declarative c.
Proof.
  intros c. split.
  - intro H. unfold classify_consensus in H.
    destruct (stage_eqb (Classification.classify c) (classify_declarative c)) eqn:E;
      [discriminate|].
    intro Habs. apply stage_eqb_eq in Habs.
    rewrite Habs in E. discriminate.
  - intro H. unfold classify_consensus.
    destruct (stage_eqb (Classification.classify c) (classify_declarative c)) eqn:E.
    + apply stage_eqb_eq in E. contradiction.
    + reflexivity.
Qed.

(* Surgical-boundary preservation through consensus: pneumoperitoneum
   forces both classifiers to IIIB, so consensus returns Some IIIB. *)
Lemma consensus_preserves_IIIB : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_consensus c = Some Stage.IIIB.
Proof.
  intros c H. apply consensus_some_iff. split.
  - apply Classification.pneumoperitoneum_forces_IIIB. exact H.
  - apply classify_declarative_IIIB_on_perf. exact H.
Qed.

(* Consensus is at least as conservative as either classifier:
   if consensus returns Some s, both individual classifiers agree on s. *)
Lemma consensus_dominated_by_each : forall c s,
  classify_consensus c = Some s ->
  Stage.leb (Classification.classify c) s = true /\
  Stage.leb (classify_declarative c) s = true.
Proof.
  intros c s H. apply consensus_some_iff in H. destruct H as [Hp Hd].
  rewrite Hp, Hd. split; apply Nat.leb_refl.
Qed.

(* Consensus is total in the sense that it always terminates with
   Some s or None — it's a deterministic decision over the two classifiers. *)
Lemma consensus_total : forall c,
  (exists s, classify_consensus c = Some s) \/ classify_consensus c = None.
Proof.
  intro c. unfold classify_consensus.
  destruct (stage_eqb _ _).
  - left. eexists. reflexivity.
  - right. reflexivity.
Qed.

(* Closure theorem: with the refined compute_radiographic_level, no
   patient with stage2a_findings alone (no PVG, no ascites, no
   pneumatosis, no pneumoperitoneum) can reach declarative IIA.
   The earlier divergence "intestinal dilation -> declarative IIA but
   procedural IA" is now provably impossible. *)
Theorem stage2a_alone_excludes_declarative_IIA : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = false ->
  RadiographicSigns.stage2b_findings (ClinicalState.radiographic c) = false ->
  RadiographicSigns.definite_nec_findings (ClinicalState.radiographic c) = false ->
  classify_declarative c <> Stage.IIA.
Proof.
  intros c Hno_perf Hno_2b Hno_pneum H.
  apply classify_declarative_IIA_requires_rad_level_2 in H.
  unfold compute_radiographic_level in H.
  rewrite Hno_perf, Hno_2b, Hno_pneum in H.
  destruct (RadiographicSigns.stage2a_findings (ClinicalState.radiographic c));
  destruct (RadiographicSigns.stage1_findings (ClinicalState.radiographic c));
  lia.
Qed.

(* Independence theorems for classify_declarative, mirroring the
   SafetyProperties suite for Classification.classify. The declarative
   classifier reads systemic, intestinal, radiographic, labs, coag, vitals;
   it does not consume hours_since_symptom_onset, neuro_status, or micro. *)

Theorem classify_declarative_independent_of_timestamp : forall c h,
  classify_declarative c =
  classify_declarative
    (ClinicalState.MkClinicalState
      (ClinicalState.risk_factors c) (ClinicalState.labs c)
      (ClinicalState.coag c) (ClinicalState.micro c)
      (ClinicalState.vitals c) (ClinicalState.systemic c)
      (ClinicalState.intestinal c) (ClinicalState.radiographic c)
      (ClinicalState.neuro_status c) h
      (ClinicalState.systemic_assessed_h c)
      (ClinicalState.intestinal_assessed_h c)
      (ClinicalState.radiographic_assessed_h c)).
Proof.
  intros c h. unfold classify_declarative, meets_criteria,
    compute_systemic_level, compute_intestinal_level,
    compute_radiographic_level.
  destruct c; reflexivity.
Qed.

Theorem classify_declarative_independent_of_neuro : forall c n,
  classify_declarative c =
  classify_declarative
    (ClinicalState.MkClinicalState
      (ClinicalState.risk_factors c) (ClinicalState.labs c)
      (ClinicalState.coag c) (ClinicalState.micro c)
      (ClinicalState.vitals c) (ClinicalState.systemic c)
      (ClinicalState.intestinal c) (ClinicalState.radiographic c)
      n (ClinicalState.hours_since_symptom_onset c)
      (ClinicalState.systemic_assessed_h c)
      (ClinicalState.intestinal_assessed_h c)
      (ClinicalState.radiographic_assessed_h c)).
Proof.
  intros c n. unfold classify_declarative, meets_criteria,
    compute_systemic_level, compute_intestinal_level,
    compute_radiographic_level.
  destruct c; reflexivity.
Qed.

(* Abstract input tuple for classify_declarative: the three computed levels
   (systemic, intestinal, radiographic) suffice to determine the stage,
   since meets_criteria reads only those levels. The faithfulness lemma
   below establishes the bridge to the concrete classifier. *)
Record ClassifierDeclInputs : Type := MkDeclCI {
  decl_ci_sys_level : nat;
  decl_ci_int_level : nat;
  decl_ci_rad_level : nat
}.

Definition extract_decl_ci (c : ClinicalState.t) : ClassifierDeclInputs :=
  MkDeclCI
    (compute_systemic_level c)
    (compute_intestinal_level (ClinicalState.intestinal c))
    (compute_radiographic_level (ClinicalState.radiographic c)).

(* Level-based reformulation of classify_declarative. Each stage's criteria
   are translated into a level threshold on the abstract input. *)
Definition classify_decl_inputs (ci : ClassifierDeclInputs) : Stage.t :=
  if 3 <=? decl_ci_rad_level ci then Stage.IIIB
  else if (3 <=? decl_ci_sys_level ci) && (3 <=? decl_ci_int_level ci) &&
          (2 <=? decl_ci_rad_level ci) then Stage.IIIA
  else if (2 <=? decl_ci_sys_level ci) && (2 <=? decl_ci_int_level ci) &&
          (2 <=? decl_ci_rad_level ci) then Stage.IIB
  else if (1 <=? decl_ci_sys_level ci) && (2 <=? decl_ci_int_level ci) &&
          (2 <=? decl_ci_rad_level ci) then Stage.IIA
  else if (1 <=? decl_ci_sys_level ci) && (1 <=? decl_ci_int_level ci) && true
       then Stage.IB
  else Stage.IA.

Lemma classify_decl_inputs_faithful : forall c,
  classify_decl_inputs (extract_decl_ci c) = classify_declarative c.
Proof.
  intros c. unfold classify_decl_inputs, extract_decl_ci, classify_declarative,
    meets_criteria, stage_IIIB_criteria, stage_IIIA_criteria, stage_IIB_criteria,
    stage_IIA_criteria, stage_IB_criteria, stage_IA_criteria.
  cbn.
  reflexivity.
Qed.

(* Component-wise subset relation. *)
Definition decl_ci_subset (c1 c2 : ClassifierDeclInputs) : Prop :=
  decl_ci_sys_level c1 <= decl_ci_sys_level c2 /\
  decl_ci_int_level c1 <= decl_ci_int_level c2 /\
  decl_ci_rad_level c1 <= decl_ci_rad_level c2.

(* Monotonicity: increasing any level cannot decrease the resulting stage. *)
Lemma classify_decl_inputs_monotone : forall c1 c2,
  decl_ci_subset c1 c2 ->
  Stage.leb (classify_decl_inputs c1) (classify_decl_inputs c2) = true.
Proof.
  intros c1 c2 [Hsys [Hint Hrad]].
  unfold classify_decl_inputs.
  destruct (3 <=? decl_ci_rad_level c1) eqn:E1_IIIB.
  - apply Nat.leb_le in E1_IIIB.
    assert (E2 : 3 <=? decl_ci_rad_level c2 = true) by (apply Nat.leb_le; lia).
    rewrite E2. reflexivity.
  - destruct (3 <=? decl_ci_rad_level c2) eqn:E2_IIIB.
    + (* c1 < IIIB, c2 = IIIB *)
      destruct ((3 <=? decl_ci_sys_level c1) && (3 <=? decl_ci_int_level c1) &&
                (2 <=? decl_ci_rad_level c1));
      destruct ((2 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                (2 <=? decl_ci_rad_level c1));
      destruct ((1 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                (2 <=? decl_ci_rad_level c1));
      destruct ((1 <=? decl_ci_sys_level c1) && (1 <=? decl_ci_int_level c1) && true);
      reflexivity.
    + (* Neither at IIIB *)
      destruct ((3 <=? decl_ci_sys_level c1) && (3 <=? decl_ci_int_level c1) &&
                (2 <=? decl_ci_rad_level c1)) eqn:E1_IIIA.
      * apply andb_true_iff in E1_IIIA. destruct E1_IIIA as [E1a Erad].
        apply andb_true_iff in E1a. destruct E1a as [Esys Eint].
        apply Nat.leb_le in Esys, Eint, Erad.
        assert (S2 : 3 <=? decl_ci_sys_level c2 = true) by (apply Nat.leb_le; lia).
        assert (I2 : 3 <=? decl_ci_int_level c2 = true) by (apply Nat.leb_le; lia).
        assert (R2 : 2 <=? decl_ci_rad_level c2 = true) by (apply Nat.leb_le; lia).
        rewrite S2, I2, R2. reflexivity.
      * destruct ((3 <=? decl_ci_sys_level c2) && (3 <=? decl_ci_int_level c2) &&
                  (2 <=? decl_ci_rad_level c2)).
        { destruct ((2 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                    (2 <=? decl_ci_rad_level c1));
          destruct ((1 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                    (2 <=? decl_ci_rad_level c1));
          destruct ((1 <=? decl_ci_sys_level c1) && (1 <=? decl_ci_int_level c1) && true);
          reflexivity. }
        destruct ((2 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                  (2 <=? decl_ci_rad_level c1)) eqn:E1_IIB.
        { apply andb_true_iff in E1_IIB. destruct E1_IIB as [E1a Erad].
          apply andb_true_iff in E1a. destruct E1a as [Esys Eint].
          apply Nat.leb_le in Esys, Eint, Erad.
          assert (S2 : 2 <=? decl_ci_sys_level c2 = true) by (apply Nat.leb_le; lia).
          assert (I2 : 2 <=? decl_ci_int_level c2 = true) by (apply Nat.leb_le; lia).
          assert (R2 : 2 <=? decl_ci_rad_level c2 = true) by (apply Nat.leb_le; lia).
          rewrite S2, I2, R2. simpl. reflexivity. }
        destruct ((2 <=? decl_ci_sys_level c2) && (2 <=? decl_ci_int_level c2) &&
                  (2 <=? decl_ci_rad_level c2)).
        { destruct ((1 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                    (2 <=? decl_ci_rad_level c1));
          destruct ((1 <=? decl_ci_sys_level c1) && (1 <=? decl_ci_int_level c1) && true);
          reflexivity. }
        destruct ((1 <=? decl_ci_sys_level c1) && (2 <=? decl_ci_int_level c1) &&
                  (2 <=? decl_ci_rad_level c1)) eqn:E1_IIA.
        { apply andb_true_iff in E1_IIA. destruct E1_IIA as [E1a Erad].
          apply andb_true_iff in E1a. destruct E1a as [Esys Eint].
          apply Nat.leb_le in Esys, Eint, Erad.
          assert (S2 : 1 <=? decl_ci_sys_level c2 = true) by (apply Nat.leb_le; lia).
          assert (I2 : 2 <=? decl_ci_int_level c2 = true) by (apply Nat.leb_le; lia).
          assert (R2 : 2 <=? decl_ci_rad_level c2 = true) by (apply Nat.leb_le; lia).
          rewrite S2, I2, R2. simpl. reflexivity. }
        destruct ((1 <=? decl_ci_sys_level c2) && (2 <=? decl_ci_int_level c2) &&
                  (2 <=? decl_ci_rad_level c2)).
        { destruct ((1 <=? decl_ci_sys_level c1) && (1 <=? decl_ci_int_level c1) && true);
          reflexivity. }
        destruct ((1 <=? decl_ci_sys_level c1) && (1 <=? decl_ci_int_level c1) && true) eqn:E1_IB.
        { apply andb_true_iff in E1_IB. destruct E1_IB as [E1a _].
          apply andb_true_iff in E1a. destruct E1a as [Esys Eint].
          apply Nat.leb_le in Esys, Eint.
          assert (S2 : 1 <=? decl_ci_sys_level c2 = true) by (apply Nat.leb_le; lia).
          assert (I2 : 1 <=? decl_ci_int_level c2 = true) by (apply Nat.leb_le; lia).
          rewrite S2, I2. simpl. reflexivity. }
        destruct ((1 <=? decl_ci_sys_level c2) && (1 <=? decl_ci_int_level c2) && true);
        reflexivity.
Qed.

(* Synthesis classifier: conservative join of procedural and declarative
   readings. Returns the higher of the two stages, dominating both
   classifiers. Useful when callers want maximum sensitivity over the
   principled disagreement region. *)
Definition classify_synthesis (c : ClinicalState.t) : Stage.t :=
  let s_proc := Classification.classify c in
  let s_decl := classify_declarative c in
  if Stage.leb s_proc s_decl then s_decl else s_proc.

Lemma classify_synthesis_dominates_proc : forall c,
  Stage.leb (Classification.classify c) (classify_synthesis c) = true.
Proof.
  intros c. unfold classify_synthesis.
  destruct (Stage.leb (Classification.classify c) (classify_declarative c)) eqn:E.
  - exact E.
  - unfold Stage.leb. apply Nat.leb_le. lia.
Qed.

Lemma classify_synthesis_dominates_decl : forall c,
  Stage.leb (classify_declarative c) (classify_synthesis c) = true.
Proof.
  intros c. unfold classify_synthesis.
  destruct (Stage.leb (Classification.classify c) (classify_declarative c)) eqn:E.
  - unfold Stage.leb. apply Nat.leb_refl.
  - unfold Stage.leb in *. apply Nat.leb_gt in E. apply Nat.leb_le. lia.
Qed.

Lemma classify_synthesis_preserves_IIIB : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_synthesis c = Stage.IIIB.
Proof.
  intros c H. unfold classify_synthesis.
  rewrite (Classification.pneumoperitoneum_forces_IIIB c H).
  rewrite (classify_declarative_IIIB_on_perf c H).
  reflexivity.
Qed.

Theorem classify_declarative_independent_of_micro : forall c m,
  classify_declarative c =
  classify_declarative
    (ClinicalState.MkClinicalState
      (ClinicalState.risk_factors c) (ClinicalState.labs c)
      (ClinicalState.coag c) m
      (ClinicalState.vitals c) (ClinicalState.systemic c)
      (ClinicalState.intestinal c) (ClinicalState.radiographic c)
      (ClinicalState.neuro_status c) (ClinicalState.hours_since_symptom_onset c)
      (ClinicalState.systemic_assessed_h c)
      (ClinicalState.intestinal_assessed_h c)
      (ClinicalState.radiographic_assessed_h c)).
Proof.
  intros c m. unfold classify_declarative, meets_criteria,
    compute_systemic_level, compute_intestinal_level,
    compute_radiographic_level.
  destruct c; reflexivity.
Qed.

End BellCriteria.
