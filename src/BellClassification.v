From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.

Import ListNotations.

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

(* DESIGN DECISION: classify_stage does NOT require systemic signs for
   Stage IIA or IIB. This deviates from Bell's original 1978 criteria which
   require systemic signs at all stages.
   Rationale: the procedural classifier prioritizes radiographic and
   intestinal findings as the primary staging drivers because:
   1. Pneumatosis (IIA) and portal venous gas (IIB) are pathognomonic
      regardless of systemic status.
   2. Some neonates develop definite NEC radiographically before systemic
      signs manifest (Kliegman & Walsh 1987, Pediatr Clin North Am 34:1).
   3. Waiting for systemic signs to classify could delay treatment.
   Witness 3 (line ~3700) demonstrates IIB classification with systemic = none.
   The alternative classify_declarative enforces systemic requirements via
   level thresholds. See classify_agree_on_surgery for the safety guarantee
   that both agree on the surgical boundary (IIIB).

   IIIA radiographic requirement.
   classify_stage requires stage2a_findings || stage2b_findings for IIIA,
   which includes intestinal_dilation (a nonspecific finding) alone.
   This is intentional: in the context of stage3 systemic signs AND
   stage3 intestinal signs, even nonspecific radiographic changes
   support the IIIA classification. Pneumatosis is not required. *)
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

(* Staleness-guarded classifier: returns None if signs are stale *)
Definition classify_checked (c : ClinicalState.t) : option Stage.t :=
  if ClinicalState.signs_current c then Some (classify_stage c)
  else None.

Lemma classify_checked_requires_current : forall c s,
  classify_checked c = Some s -> ClinicalState.signs_current c = true.
Proof.
  intros c s H. unfold classify_checked in H.
  destruct (ClinicalState.signs_current c) eqn:E.
  - reflexivity.
  - discriminate.
Qed.

Lemma classify_checked_agrees : forall c,
  ClinicalState.signs_current c = true ->
  classify_checked c = Some (classify c).
Proof.
  intros c H. unfold classify_checked. rewrite H. reflexivity.
Qed.

(* Type-safe classifier: only accepts freshness-witnessed states.
   Returns a stage directly (no option) since freshness is guaranteed. *)
Definition classify_current (c : ClinicalState.current_t) : Stage.t :=
  classify (ClinicalState.current_state c).

Lemma classify_current_agrees : forall c,
  classify_current c = classify (ClinicalState.current_state c).
Proof. reflexivity. Qed.

Lemma pneumoperitoneum_forces_IIIB : forall c,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify c = Stage.IIIB.
Proof.
  intros c H. unfold classify, classify_stage. rewrite H. reflexivity.
Qed.

Lemma classify_always_valid : forall c,
  1 <= Stage.to_nat (classify c) <= Stage.stage_count.
Proof.
  intros c; unfold Stage.stage_count; split;
  destruct (classify c); simpl; lia.
Qed.

(* The default fall-through of classify_stage is Stage.IA — the mildest
   stage. This is conservative: when no staging pattern matches, the
   classifier avoids overtreating by defaulting to suspected NEC rather
   than definite or advanced NEC. *)
Lemma classify_default_is_mildest : forall c,
  Stage.to_nat (classify c) >= Stage.to_nat Stage.IA.
Proof. intros c. destruct (classify c); simpl; lia. Qed.

(* Completeness: ConfirmedNEC requires findings and stage >= IIA *)
Lemma confirmed_nec_has_findings : forall c s,
  diagnose c = Diagnosis.ConfirmedNEC s ->
  has_any_findings c = true.
Proof.
  intros c s H. unfold diagnose in H.
  destruct (negb (has_any_findings c)) eqn:E.
  - discriminate.
  - apply Bool.negb_false_iff in E. exact E.
Qed.

Lemma confirmed_nec_stage_ge_IIA : forall c s,
  diagnose c = Diagnosis.ConfirmedNEC s ->
  Stage.to_nat s >= 3.
Proof.
  intros c s H. unfold diagnose in H.
  destruct (negb (has_any_findings c)); [discriminate|].
  destruct (RadiographicSigns.pneumoperitoneum _ && _)%bool; [discriminate|].
  destruct (classify_stage c) eqn:Ec; try discriminate;
  inversion H; subst; simpl; lia.
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

(* urgency_from_trajectory is monotone in stage for each
   fixed trajectory. IIIB always produces Emergent regardless of
   trajectory because pneumoperitoneum is an absolute surgical indication. *)
Definition urgency_from_trajectory (traj : TemporalProgression.ClinicalTrajectory)
    (current_stage : Stage.t) : UrgencyLevel :=
  match traj, current_stage with
  | _, Stage.IIIB => Emergent
  | TemporalProgression.RapidDeterioration, _ => Emergent
  | TemporalProgression.Worsening, Stage.IIIA => Emergent
  | TemporalProgression.Worsening, Stage.IIB => Urgent
  | TemporalProgression.Worsening, Stage.IIA => Elevated
  | TemporalProgression.Worsening, _ => Elevated
  | TemporalProgression.Stable, Stage.IIIA => Urgent
  | TemporalProgression.Stable, Stage.IIB => Elevated
  | TemporalProgression.Stable, _ => Routine
  | TemporalProgression.Improving, _ => Routine
  end.

(* Organ-failure-modified urgency: multiorgan dysfunction escalates urgency *)
Definition urgency_with_organ_failure
    (base_urgency : UrgencyLevel)
    (organ_assessment : NeonatalOrganFailure.OrganFailureAssessment) : UrgencyLevel :=
  if NeonatalOrganFailure.multiorgan_dysfunction organ_assessment then
    match base_urgency with
    | Routine => Elevated
    | Elevated => Urgent
    | Urgent => Emergent
    | Emergent => Emergent
    end
  else base_urgency.

Lemma mods_escalates_urgency : forall u oa,
  NeonatalOrganFailure.multiorgan_dysfunction oa = true ->
  urgency_with_organ_failure u oa <> Routine.
Proof.
  intros u oa Hmods. unfold urgency_with_organ_failure.
  rewrite Hmods. destruct u; discriminate.
Qed.

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
Proof. solve_stage. Qed.

(* Urgency monotonicity in stage for a fixed trajectory.
   For worsening/rapid trajectories, higher stages produce equal or
   higher urgency. For stable/improving, urgency is constant except
   at IIIA/IIIB thresholds. *)
Definition urgency_to_nat (u : UrgencyLevel) : nat :=
  match u with
  | Routine => 0
  | Elevated => 1
  | Urgent => 2
  | Emergent => 3
  end.

Lemma urgency_monotone_rapid_deterioration : forall s1 s2,
  Stage.leb s1 s2 = true ->
  urgency_to_nat (urgency_from_trajectory TemporalProgression.RapidDeterioration s1) <=
  urgency_to_nat (urgency_from_trajectory TemporalProgression.RapidDeterioration s2).
Proof. solve_stage_pair. Qed.

Lemma urgency_monotone_worsening : forall s1 s2,
  Stage.leb s1 s2 = true ->
  urgency_to_nat (urgency_from_trajectory TemporalProgression.Worsening s1) <=
  urgency_to_nat (urgency_from_trajectory TemporalProgression.Worsening s2).
Proof. solve_stage_pair. Qed.

Lemma urgency_monotone_stable : forall s1 s2,
  Stage.leb s1 s2 = true ->
  urgency_to_nat (urgency_from_trajectory TemporalProgression.Stable s1) <=
  urgency_to_nat (urgency_from_trajectory TemporalProgression.Stable s2).
Proof. solve_stage_pair. Qed.

(* Reassessment hours are monotonically decreasing with urgency.
   Higher urgency -> shorter reassessment interval. *)
Lemma reassess_decreasing_by_urgency : forall u1 u2,
  urgency_to_nat u1 <= urgency_to_nat u2 ->
  (* urgency -> hours mapping is: Emergent->1, Urgent->2, Elevated->4, Routine->8 *)
  let h := fun u => match u with Emergent => 1 | Urgent => 2 | Elevated => 4 | Routine => 8 end in
  h u2 <= h u1.
Proof.
  intros [] []; simpl; intro H; lia.
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
  solve_stage.
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

(* Bridge: derive SurgicalContext from ClinicalState *)
Definition surgical_context_of (c : ClinicalState.t)
    (deteriorating : bool) (paracentesis_positive : bool) : SurgicalContext :=
  let rad := ClinicalState.radiographic c in
  let int := ClinicalState.intestinal c in
  MkSurgicalContext
    (RadiographicSigns.pneumoperitoneum rad)
    false  (* fixed loop requires serial imaging — not derivable from single state *)
    (IntestinalSigns.abdominal_cellulitis int)
    deteriorating
    paracentesis_positive
    (RadiographicSigns.portal_venous_gas rad && deteriorating).

Lemma bridge_preserves_pneumoperitoneum : forall c d p,
  has_pneumoperitoneum (surgical_context_of c d p) =
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c).
Proof. reflexivity. Qed.

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

(* Refined per NET trial (Moss et al. 2006, NEJM 354:2225-2234):
   - ELBW (<1000g) and hemodynamically unstable: drain as bridge
   - ELBW stable: laparotomy preferred (NET showed equivalent outcomes)
   - >1000g: laparotomy
   Hemodynamic instability = on vasopressors or MAP < threshold *)
Definition initial_procedure_for_perforation
    (birth_weight_grams : nat) (hemodynamically_unstable : bool) : Procedure :=
  if (birth_weight_grams <? 1000) && hemodynamically_unstable
  then PrimaryPeritonealDrainage
  else ExploratoryLaparotomy.

Definition requires_stoma (extent_of_necrosis_percent : nat) : bool :=
  50 <? extent_of_necrosis_percent.

Lemma elbw_unstable_gets_drain : forall bw,
  bw < 1000 ->
  initial_procedure_for_perforation bw true = PrimaryPeritonealDrainage.
Proof.
  intros bw H. unfold initial_procedure_for_perforation.
  destruct (bw <? 1000) eqn:E.
  - reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

(* NET trial nuance: stable ELBW gets laparotomy, not drain *)
Lemma elbw_stable_gets_laparotomy : forall bw,
  bw < 1000 ->
  initial_procedure_for_perforation bw false = ExploratoryLaparotomy.
Proof.
  intros bw H. unfold initial_procedure_for_perforation.
  destruct (bw <? 1000) eqn:E; reflexivity.
Qed.

(* Non-ELBW always gets laparotomy regardless of stability *)
Lemma non_elbw_gets_laparotomy : forall bw stab,
  1000 <= bw ->
  initial_procedure_for_perforation bw stab = ExploratoryLaparotomy.
Proof.
  intros bw stab H. unfold initial_procedure_for_perforation.
  destruct (bw <? 1000) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

End SurgicalProcedures.

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

(* Culture-directed therapy: adjust regimen based on microbiology results.
   Blood culture timing fields gate escalation: no positive result after
   the escalation threshold hours triggers broadening consideration. *)
Definition culture_escalation_threshold_h : nat := 48.

(* Guarded subtraction — if collected_h > current_h (data error),
   treat as not-yet-pending rather than silently clamping to 0. *)
Definition culture_pending_too_long (m : Microbiology.t) (current_h : nat) : bool :=
  match Microbiology.blood_culture m, Microbiology.blood_culture_collected_h m with
  | Microbiology.Pending, Some collected =>
      (collected <=? current_h) &&
      (culture_escalation_threshold_h <=? (current_h - collected))
  | _, _ => false
  end.

Definition culture_directed_regimen (s : Stage.t) (m : Microbiology.t)
    (current_h : nat) : Regimen :=
  let base := recommended_regimen_by_stage s in
  if Microbiology.fungal_sepsis m then Broad_VancMeropenem
  else if Microbiology.gram_negative_sepsis m then
    match base with
    | Empiric_AmpGent => Empiric_AmpGentMetro
    | _ => base
    end
  else if culture_pending_too_long m current_h then
    match base with
    | Empiric_AmpGent => Empiric_AmpGentMetro
    | Empiric_AmpGentMetro => Broad_VancCefotaximeMetro
    | _ => base
    end
  else base.

Definition has_antifungal_coverage (r : Regimen) : bool :=
  match r with
  | Broad_VancMeropenem => true
  | _ => false
  end.

Section CultureDirectedProperties.
Variables (s : Stage.t) (m : Microbiology.t) (h : nat).

Lemma fungal_sepsis_gets_antifungal :
  Microbiology.fungal_sepsis m = true ->
  has_antifungal_coverage (culture_directed_regimen s m h) = true.
Proof.
  intros Hf. unfold culture_directed_regimen. rewrite Hf. reflexivity.
Qed.

Lemma gram_neg_gets_anaerobic :
  Microbiology.gram_negative_sepsis m = true ->
  has_anaerobic_coverage (culture_directed_regimen s m h) = true.
Proof.
  intros Hgn. unfold culture_directed_regimen.
  assert (Hfung: Microbiology.fungal_sepsis m = false).
  { unfold Microbiology.fungal_sepsis, Microbiology.gram_negative_sepsis in *.
    destruct (Microbiology.blood_culture m); try discriminate. reflexivity. }
  rewrite Hfung, Hgn.
  destruct s; reflexivity.
Qed.

Lemma culture_directed_never_weaker :
  has_anaerobic_coverage (recommended_regimen_by_stage s) = true ->
  has_anaerobic_coverage (culture_directed_regimen s m h) = true.
Proof.
  intros Hbase. unfold culture_directed_regimen.
  destruct (Microbiology.fungal_sepsis m); [reflexivity|].
  destruct (Microbiology.gram_negative_sepsis m).
  - destruct s; simpl in *; reflexivity.
  - destruct (culture_pending_too_long m h).
    + destruct s; simpl in *; try reflexivity.
    + exact Hbase.
Qed.

(* culture_directed_regimen preserves gram-negative coverage *)
Lemma culture_directed_preserves_gram_neg :
  has_gram_negative_coverage (recommended_regimen_by_stage s) = true ->
  has_gram_negative_coverage (culture_directed_regimen s m h) = true.
Proof.
  intros Hbase. unfold culture_directed_regimen.
  destruct (Microbiology.fungal_sepsis m); [reflexivity|].
  destruct (Microbiology.gram_negative_sepsis m).
  - destruct s; simpl in *; reflexivity.
  - destruct (culture_pending_too_long m h).
    + destruct s; simpl in *; reflexivity.
    + exact Hbase.
Qed.

End CultureDirectedProperties.

(* culture_directed_regimen never narrows overall spectrum.
   If the base regimen has gram-negative, anaerobic, and gram-positive
   coverage, the directed regimen preserves all three.
   Note: has_gram_positive_coverage would need a definition — all
   regimens that include Vancomycin have explicit gram-positive coverage.
   For now we prove the two defined coverage predicates are preserved. *)
Definition has_gram_positive_coverage (r : Regimen) : bool :=
  match r with
  | Broad_VancCefotaximeMetro => true
  | Broad_VancMeropenem => true
  | _ => false
  end.

Lemma culture_directed_never_narrows_anaerobic : forall s m h,
  has_anaerobic_coverage (recommended_regimen_by_stage s) = true ->
  has_anaerobic_coverage (culture_directed_regimen s m h) = true.
Proof. exact culture_directed_never_weaker. Qed.

Lemma culture_directed_never_narrows_gram_neg : forall s m h,
  has_gram_negative_coverage (recommended_regimen_by_stage s) = true ->
  has_gram_negative_coverage (culture_directed_regimen s m h) = true.
Proof. exact culture_directed_preserves_gram_neg. Qed.

Lemma advanced_nec_has_anaerobic_coverage : forall s,
  Stage.to_nat s >= 5 ->
  has_anaerobic_coverage (recommended_regimen_by_stage s) = true.
Proof.
  solve_stage.
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

(* Type-safe version: stage enum prevents invalid inputs *)
Definition npo_duration (s : Stage.t) : nat :=
  match s with
  | Stage.IA | Stage.IB => npo_stage_I
  | Stage.IIA | Stage.IIB => npo_stage_II
  | Stage.IIIA | Stage.IIIB => npo_stage_III
  end.

(* Backward-compatible nat version; out-of-range defaults to Stage III *)
Definition npo_duration_by_stage (stage_nat : nat) : nat :=
  match stage_nat with
  | 1 | 2 => npo_stage_I
  | 3 | 4 => npo_stage_II
  | 5 => npo_stage_III
  | _ => npo_stage_III
  end.

(* The two representations agree on valid stage nats *)
Lemma npo_duration_consistent : forall s,
  npo_duration s = npo_duration_by_stage (Stage.to_nat s).
Proof. solve_stage. Qed.

Definition can_restart_feeds (stage_nat : nat) (days_npo : nat)
    (abdominal_exam_normal : bool) (no_bilious_residuals : bool) : bool :=
  (npo_duration_by_stage stage_nat <=? days_npo) &&
  abdominal_exam_normal && no_bilious_residuals.

(* Provenance citations for feeding parameters.
   - Trophic feeds 20 mL/kg/day: Berseth et al. 2003, J Pediatr 143(4):500-505
   - Advancement rate 20 mL/kg/day: Hay & Thureen 2010, Clin Perinatol 37(2):259-275;
     SIFT trial (Dorling et al. 2019, NEJM 381(13):1241-1250) found no benefit
     to slower rates, supporting 20 mL/kg/day as standard.
   - Full feed target 150 mL/kg/day: Embleton et al. 2005, Arch Dis Child Fetal
     Neonatal Ed 90(3):F224-F228 *)
Definition trophic_feed_volume_ml_kg_day : nat := 20.
Definition advancement_rate_ml_kg_day : nat := 20.
Definition full_feed_volume_ml_kg_day : nat := 150.

Definition preferred_feed_type_post_nec : FeedType := BreastMilk.

Definition days_to_full_feeds (start_volume : nat) : nat :=
  (full_feed_volume_ml_kg_day - start_volume) / advancement_rate_ml_kg_day.

(* Total recovery timeline: NPO period + advancement from trophic to full *)
Definition total_recovery_days (stage_nat : nat) : nat :=
  npo_duration_by_stage stage_nat + days_to_full_feeds trophic_feed_volume_ml_kg_day.

(* Trophic feeds reach full feeds in 6 days: (150-20)/20 = 6 *)
Lemma trophic_to_full_feeds_duration :
  days_to_full_feeds trophic_feed_volume_ml_kg_day = 6.
Proof. reflexivity. Qed.

(* Total recovery is bounded: at most 20 days (Stage III NPO 14 + advancement 6) *)
Lemma total_recovery_bounded : forall stage_nat,
  total_recovery_days stage_nat <= 20.
Proof.
  intros [|[|[|[|[|[|n]]]]]]; unfold total_recovery_days, npo_duration_by_stage,
    days_to_full_feeds; simpl; lia.
Qed.

(* Higher stages require longer total recovery *)
Lemma total_recovery_monotone : forall s1 s2,
  1 <= s1 -> s1 <= s2 -> s2 <= 6 ->
  total_recovery_days s1 <= total_recovery_days s2.
Proof.
  intros [|[|[|[|[|[|s1']]]]]]; intros [|[|[|[|[|[|s2']]]]]];
  intros; unfold total_recovery_days, npo_duration_by_stage, days_to_full_feeds;
  simpl; try lia.
Qed.

(* Refeeding can only begin after NPO period: total recovery > NPO alone *)
Lemma recovery_exceeds_npo : forall stage_nat,
  1 <= stage_nat -> stage_nat <= 6 ->
  npo_duration_by_stage stage_nat < total_recovery_days stage_nat.
Proof.
  intros [|[|[|[|[|[|[|n]]]]]]]; intros H1 H2; try lia.
  all: vm_compute; lia.
Qed.

Lemma stage_IIIB_requires_14_days_npo :
  npo_duration_by_stage 6 = 14.
Proof. reflexivity. Qed.

(* Refeeding safety: during active NEC (stage >= IIA, i.e., stage_nat >= 3),
   feeds cannot restart until the NPO period has elapsed. At diagnosis
   (days_npo = 0), can_restart_feeds is always false. *)
Lemma no_refeeding_during_active_nec : forall stage_nat,
  3 <= stage_nat -> stage_nat <= 6 ->
  can_restart_feeds stage_nat 0 true true = false.
Proof.
  intros [|[|[|[|[|[|[|n]]]]]]]; intros H1 H2;
  try lia; vm_compute; reflexivity.
Qed.

(* Stronger: feeds cannot restart until at least npo_duration days have passed *)
Lemma refeeding_requires_npo_elapsed : forall stage_nat days exam resid,
  can_restart_feeds stage_nat days exam resid = true ->
  npo_duration_by_stage stage_nat <= days.
Proof.
  intros stage_nat days exam resid H.
  unfold can_restart_feeds in H.
  apply andb_true_iff in H. destruct H as [H1 _].
  apply andb_true_iff in H1. destruct H1 as [H1 _].
  apply Nat.leb_le in H1. exact H1.
Qed.

(* Converse of refeeding_requires_npo_elapsed:
   NPO elapsed + normal abdominal exam + no bilious residuals
   is sufficient to restart feeds. *)
Lemma refeeding_sufficient : forall stage_nat days,
  npo_duration_by_stage stage_nat <= days ->
  can_restart_feeds stage_nat days true true = true.
Proof.
  intros stage_nat days H.
  unfold can_restart_feeds. simpl.
  apply Nat.leb_le in H. rewrite H. reflexivity.
Qed.

End FeedingProtocol.

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
Proof. solve_stage. Qed.

Lemma definite_category_2 : forall s,
  is_definite s = true -> category s = 2.
Proof. solve_stage. Qed.

Lemma advanced_category_3 : forall s,
  is_advanced s = true -> category s = 3.
Proof. solve_stage. Qed.

Lemma stage_nat_determines_category : forall s,
  category s = (Stage.to_nat s + 1) / 2.
Proof. solve_stage. Qed.

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

(* Risk ranges reflecting published uncertainty rather than point estimates *)
Record RiskRange : Type := MkRiskRange {
  low : nat;
  mid : nat;
  high : nat
}.

Definition valid_range (r : RiskRange) : Prop :=
  low r <= mid r /\ mid r <= high r.

(* Provenance citations for risk range endpoints.
   Mortality ranges (percent):
   Stage I: 0% (Fitzgibbons 2009: <1% for suspected NEC)
   Stage IB high: 2% (Holman et al. 2006, J Perinatol 26(7):392-396)
   Stage IIA: 2-10% (Fitzgibbons 2009: 10% for definite NEC without surgery)
   Stage IIB: 5-15% (Neu 2011: 10-15% for definite NEC with systemic compromise)
   Stage IIIA: 15-30% (Fitzgibbons 2009: 20-30% for advanced NEC)
   Stage IIIB: 20-50% (Neu 2011: 30-50% for NEC requiring surgery) *)
Definition mortality_risk (s : Stage.t) : RiskRange :=
  match s with
  | Stage.IA => MkRiskRange 0 0 0
  | Stage.IB => MkRiskRange 0 0 2
  | Stage.IIA => MkRiskRange 2 5 10
  | Stage.IIB => MkRiskRange 5 10 15
  | Stage.IIIA => MkRiskRange 15 20 30
  | Stage.IIIB => MkRiskRange 20 30 50
  end.

(* Backward-compatible midpoint accessor *)
Definition mortality_risk_percent (s : Stage.t) : nat :=
  mid (mortality_risk s).

(* Stricture ranges (Horwitz 1995, Butter 2006) *)
Definition stricture_risk (s : Stage.t) : RiskRange :=
  match s with
  | Stage.IA => MkRiskRange 0 0 0
  | Stage.IB => MkRiskRange 0 0 5
  | Stage.IIA => MkRiskRange 5 10 15
  | Stage.IIB => MkRiskRange 10 20 30
  | Stage.IIIA => MkRiskRange 15 25 35
  | Stage.IIIB => MkRiskRange 25 35 45
  end.

Definition stricture_risk_percent (s : Stage.t) : nat :=
  mid (stricture_risk s).

(* SBS ranges (Cole 2008, Wales 2010) *)
Definition short_bowel_risk (s : Stage.t) : RiskRange :=
  match s with
  | Stage.IA => MkRiskRange 0 0 0
  | Stage.IB => MkRiskRange 0 0 0
  | Stage.IIA => MkRiskRange 0 0 2
  | Stage.IIB => MkRiskRange 2 5 10
  | Stage.IIIA => MkRiskRange 5 10 15
  | Stage.IIIB => MkRiskRange 15 25 35
  end.

Definition short_bowel_risk_percent (s : Stage.t) : nat :=
  mid (short_bowel_risk s).

(* All risk ranges are valid *)
Lemma mortality_risk_valid : forall s, valid_range (mortality_risk s).
Proof. unfold valid_range; solve_stage. Qed.

Lemma stricture_risk_valid : forall s, valid_range (stricture_risk s).
Proof. unfold valid_range; solve_stage. Qed.

Lemma short_bowel_risk_valid : forall s, valid_range (short_bowel_risk s).
Proof. unfold valid_range; solve_stage. Qed.

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
Proof. solve_stage. Qed.

Lemma suspected_nec_no_mortality :
  forall s, StageProgression.is_suspected s = true -> mortality_risk_percent s = 0.
Proof. solve_stage. Qed.

Lemma definite_nec_requires_followup :
  forall s, StageProgression.is_definite s = true -> requires_long_term_followup s = true.
Proof. solve_stage. Qed.

Lemma higher_stage_worse_mortality : forall s1 s2,
  Stage.leb s1 s2 = true ->
  mortality_risk_percent s1 <= mortality_risk_percent s2.
Proof.
  intros [] []; vm_compute; intro H; try lia; discriminate.
Qed.

Lemma higher_stage_worse_stricture : forall s1 s2,
  Stage.leb s1 s2 = true ->
  stricture_risk_percent s1 <= stricture_risk_percent s2.
Proof.
  intros [] []; vm_compute; intro H; try lia; discriminate.
Qed.

(* Parameterized risk functions.
   Institutions can substitute era-specific or local data
   without modifying definitions. *)
Record InstitutionalRiskData : Type := MkInstitutionalRisk {
  inst_mortality : Stage.t -> RiskRange;
  inst_stricture : Stage.t -> RiskRange;
  inst_short_bowel : Stage.t -> RiskRange
}.

Definition default_institutional_data : InstitutionalRiskData :=
  MkInstitutionalRisk mortality_risk stricture_risk short_bowel_risk.

Definition inst_mortality_percent (d : InstitutionalRiskData) (s : Stage.t) : nat :=
  mid (inst_mortality d s).

Definition inst_stricture_percent (d : InstitutionalRiskData) (s : Stage.t) : nat :=
  mid (inst_stricture d s).

Definition inst_short_bowel_percent (d : InstitutionalRiskData) (s : Stage.t) : nat :=
  mid (inst_short_bowel d s).

End Prognosis.

Module OrganFailureFeedback.

(* Feed NeonatalOrganFailure scores back into staging.
   Stage III clinically requires systemic compromise. This module
   provides a staging modifier based on organ failure assessment. *)

Definition stage_with_organ_failure
    (base_stage : Stage.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : Stage.t :=
  if NeonatalOrganFailure.multiorgan_dysfunction oa then
    (* MODS pushes suspected/definite NEC to at least IIIA *)
    match base_stage with
    | Stage.IA | Stage.IB | Stage.IIA | Stage.IIB => Stage.IIIA
    | Stage.IIIA => Stage.IIIA
    | Stage.IIIB => Stage.IIIB
    end
  else base_stage.

Lemma organ_failure_never_decreases_stage : forall s oa,
  Stage.to_nat s <= Stage.to_nat (stage_with_organ_failure s oa).
Proof.
  intros s oa. unfold stage_with_organ_failure.
  destruct (NeonatalOrganFailure.multiorgan_dysfunction oa);
  solve_stage.
Qed.

Lemma mods_forces_at_least_IIIA : forall s oa,
  NeonatalOrganFailure.multiorgan_dysfunction oa = true ->
  5 <= Stage.to_nat (stage_with_organ_failure s oa).
Proof.
  intros s oa H. unfold stage_with_organ_failure.
  rewrite H. destruct s; simpl; lia.
Qed.

End OrganFailureFeedback.
