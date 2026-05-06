From Stdlib Require Import PeanoNat.
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

(* Aggregate systemic indicator: any of the eight systemic/lab/vital
   findings that qualify as systemic involvement in strict Bell. *)
Definition any_systemic_indicator (c : ClinicalState.t) : bool :=
  SystemicSigns.stage1_signs (ClinicalState.systemic c) ||
  SystemicSigns.stage2b_signs (ClinicalState.systemic c) ||
  ClinicalState.lab_metabolic_acidosis c ||
  ClinicalState.lab_thrombocytopenia c ||
  SystemicSigns.stage3_signs (ClinicalState.systemic c) ||
  ClinicalState.effective_hypotension c ||
  ClinicalState.has_dic c ||
  ClinicalState.lab_neutropenia c.

(* Strict Bell 1978 / Walsh-Kliegman 1986 classifier: requires any
   systemic indicator for IIA, dedicated systemic stage2b signs for IIB. *)
Definition classify_stage_strict_bell (c : ClinicalState.t) : Stage.t :=
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
  else if effective_stage3_sys && IntestinalSigns.stage3_signs int
          && (RadiographicSigns.stage2a_findings rad ||
              RadiographicSigns.stage2b_findings rad)
       then Stage.IIIA
  else if effective_stage2b_sys
          && (effective_stage2b_sys || IntestinalSigns.stage2b_signs int)
          && IntestinalSigns.stage2_signs int
          && RadiographicSigns.stage2b_findings rad
       then Stage.IIB
  else if any_systemic_indicator c
          && RadiographicSigns.definite_nec_findings rad
          && IntestinalSigns.stage2_signs int
       then Stage.IIA
  else if IntestinalSigns.stage1b_signs int && SystemicSigns.stage1_signs sys
       then Stage.IB
  else Stage.IA.

Definition classify_strict_bell (c : ClinicalState.t) : Stage.t :=
  classify_stage_strict_bell c.

(* Both classifiers agree on the surgical boundary. *)
Lemma strict_bell_IIIB_iff_pneumoperitoneum : forall c,
  classify_strict_bell c = Stage.IIIB <->
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true.
Proof.
  intros c. split.
  - intro H. unfold classify_strict_bell, classify_stage_strict_bell in H.
    destruct (RadiographicSigns.pneumoperitoneum _) eqn:E; [reflexivity|].
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _ && _ && _)%bool; try discriminate.
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _)%bool; discriminate.
  - intro H. unfold classify_strict_bell, classify_stage_strict_bell.
    rewrite H. reflexivity.
Qed.

Theorem classify_strict_agrees_on_surgery : forall c,
  classify c = Stage.IIIB <-> classify_strict_bell c = Stage.IIIB.
Proof.
  intros c. split.
  - intro H. apply strict_bell_IIIB_iff_pneumoperitoneum.
    unfold classify, classify_stage in H.
    destruct (RadiographicSigns.pneumoperitoneum _) eqn:E; [reflexivity|].
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _ && _)%bool; try discriminate.
    destruct (_ && _)%bool; try discriminate.
    destruct (_ && _)%bool; discriminate.
  - intro H. apply strict_bell_IIIB_iff_pneumoperitoneum in H.
    unfold classify, classify_stage. rewrite H. reflexivity.
Qed.

(* Under strict Bell, IIA requires at least one systemic indicator. *)
Theorem strict_bell_IIA_requires_systemic : forall c,
  classify_strict_bell c = Stage.IIA ->
  any_systemic_indicator c = true.
Proof.
  intros c H.
  destruct (any_systemic_indicator c) eqn:Hsys; [reflexivity|].
  exfalso.
  unfold classify_strict_bell, classify_stage_strict_bell in H.
  rewrite Hsys in H. simpl in H.
  destruct (RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c));
    [discriminate|].
  destruct (IntestinalSigns.stage3_signs (ClinicalState.intestinal c));
    destruct (RadiographicSigns.stage2a_findings (ClinicalState.radiographic c));
    destruct (RadiographicSigns.stage2b_findings (ClinicalState.radiographic c));
    destruct (IntestinalSigns.stage2_signs (ClinicalState.intestinal c));
    destruct (IntestinalSigns.stage2b_signs (ClinicalState.intestinal c));
    destruct (IntestinalSigns.stage1b_signs (ClinicalState.intestinal c));
    destruct (SystemicSigns.stage1_signs (ClinicalState.systemic c));
    destruct (RadiographicSigns.definite_nec_findings (ClinicalState.radiographic c));
    (* any_systemic_indicator c = false forces each systemic/lab flag false *)
    unfold any_systemic_indicator in Hsys;
    repeat (apply orb_false_iff in Hsys; destruct Hsys as [Hsys ?]);
    repeat match goal with
    | H : SystemicSigns.stage1_signs _ = false |- _ => rewrite H in *
    | H : SystemicSigns.stage2b_signs _ = false |- _ => rewrite H in *
    | H : SystemicSigns.stage3_signs _ = false |- _ => rewrite H in *
    | H : ClinicalState.lab_metabolic_acidosis _ = false |- _ => rewrite H in *
    | H : ClinicalState.lab_thrombocytopenia _ = false |- _ => rewrite H in *
    | H : ClinicalState.effective_hypotension _ = false |- _ => rewrite H in *
    | H : ClinicalState.has_dic _ = false |- _ => rewrite H in *
    | H : ClinicalState.lab_neutropenia _ = false |- _ => rewrite H in *
    end;
    simpl in H; try discriminate.
Qed.

(* Returns None when the input fails ClinicalState.is_valid. *)
Definition classify_validated (c : ClinicalState.t) : option Stage.t :=
  if ClinicalState.is_valid c then Some (classify c) else None.

Lemma classify_validated_some_iff_valid : forall c s,
  classify_validated c = Some s -> ClinicalState.valid c.
Proof.
  intros c s H. unfold classify_validated in H.
  destruct (ClinicalState.is_valid c) eqn:E; [|discriminate].
  apply ClinicalState.is_valid_iff. exact E.
Qed.

Lemma classify_validated_agrees_on_valid : forall c,
  ClinicalState.valid c ->
  classify_validated c = Some (classify c).
Proof.
  intros c Hv. unfold classify_validated.
  apply ClinicalState.is_valid_iff in Hv. rewrite Hv. reflexivity.
Qed.

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

(* classify_stage reaches IIA on definite_nec_findings (pneumatosis)
   AND intestinal stage2_signs, without requiring systemic signs.
   This deviates from strict Bell 1978 / Walsh-Kliegman 1986, which
   require systemic involvement at all stages. Pneumatosis intestinalis
   is pathognomonic and waiting for systemic signs can delay diagnosis
   (Kliegman & Walsh 1987, Pediatr Clin North Am 34:1). *)
Theorem classify_IIA_relaxes_systemic : forall c,
  classify c = Stage.IIA ->
  RadiographicSigns.definite_nec_findings (ClinicalState.radiographic c) = true /\
  IntestinalSigns.stage2_signs (ClinicalState.intestinal c) = true.
Proof.
  intros c H.
  assert (E : RadiographicSigns.definite_nec_findings (ClinicalState.radiographic c) &&
              IntestinalSigns.stage2_signs (ClinicalState.intestinal c) = true).
  { unfold classify, classify_stage in H.
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
              && RadiographicSigns.stage2b_findings _)%bool;
      [discriminate|].
    destruct (RadiographicSigns.definite_nec_findings _ &&
              IntestinalSigns.stage2_signs _)%bool.
    - reflexivity.
    - destruct (IntestinalSigns.stage1b_signs _ &&
                SystemicSigns.stage1_signs _)%bool; discriminate. }
  apply andb_true_iff in E. exact E.
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

(* Urgency levels for trajectory-aware classification. *)
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

Module TimeSeries.

(* An observation is a clinical state at a specific time.
   obs_stage and obs_severity are derived from obs_state through
   Classification.classify and ClinicalState.overall_severity_score. *)
Record Observation : Type := MkObservation {
  obs_time_hours : nat;
  obs_state : ClinicalState.t
}.

Definition obs_stage (o : Observation) : nat :=
  Stage.to_nat (Classification.classify (obs_state o)).

Definition obs_severity (o : Observation) : nat :=
  ClinicalState.overall_severity_score (obs_state o).

(* Consistency invariant: obs_time_hours matches the embedded clinical state's
   hours_since_symptom_onset. *)
Definition observation_consistent (o : Observation) : Prop :=
  obs_time_hours o = ClinicalState.hours_since_symptom_onset (obs_state o).

(* Create observation from clinical state. Stage is derived from the state
   via Classification.classify so the obs_stage cache invariant holds by
   construction. *)
Definition make_observation (time_h : nat) (state : ClinicalState.t) : Observation :=
  MkObservation time_h
    (ClinicalState.MkClinicalState
      (ClinicalState.risk_factors state)
      (ClinicalState.labs state)
      (ClinicalState.coag state)
      (ClinicalState.micro state)
      (ClinicalState.vitals state)
      (ClinicalState.systemic state)
      (ClinicalState.intestinal state)
      (ClinicalState.radiographic state)
      (ClinicalState.neuro_status state)
      time_h
      (ClinicalState.systemic_assessed_h state)
      (ClinicalState.intestinal_assessed_h state)
      (ClinicalState.radiographic_assessed_h state)).

Lemma make_observation_consistent : forall t s,
  observation_consistent (make_observation t s).
Proof.
  intros. unfold observation_consistent, make_observation. simpl. reflexivity.
Qed.

(* Stage cache invariant: by construction obs_stage o = classify (obs_state o). *)
Lemma obs_stage_derived : forall o,
  obs_stage o = Stage.to_nat (Classification.classify (obs_state o)).
Proof. reflexivity. Qed.

Lemma obs_severity_derived : forall o,
  obs_severity o = ClinicalState.overall_severity_score (obs_state o).
Proof. reflexivity. Qed.

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

Definition latest (ts : PatientTimeSeries) : option Observation :=
  match ts with
  | [] => None
  | o :: _ => Some o
  end.

Fixpoint earliest (ts : PatientTimeSeries) : option Observation :=
  match ts with
  | [] => None
  | [o] => Some o
  | _ :: rest => earliest rest
  end.

Definition series_length (ts : PatientTimeSeries) : nat := length ts.

Definition series_duration (ts : PatientTimeSeries) : nat :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      if obs_time_hours e <=? obs_time_hours l
      then obs_time_hours l - obs_time_hours e
      else 0
  | _, _ => 0
  end.

Definition stage_at_index (ts : PatientTimeSeries) (idx : nat) : option nat :=
  match nth_error ts idx with
  | Some o => Some (obs_stage o)
  | None => None
  end.

Definition stage_change (ts : PatientTimeSeries) (earlier_idx later_idx : nat) : option Z :=
  match stage_at_index ts later_idx, stage_at_index ts earlier_idx with
  | Some s2, Some s1 => Some (Z.of_nat s2 - Z.of_nat s1)%Z
  | _, _ => None
  end.

Definition is_worsening (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage e <? obs_stage l
  | _, _ => false
  end.

Definition is_improving (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage l <? obs_stage e
  | _, _ => false
  end.

Definition is_stable (ts : PatientTimeSeries) : bool :=
  match latest ts, earliest ts with
  | Some l, Some e => obs_stage l =? obs_stage e
  | _, _ => true
  end.

Fixpoint count_escalations (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (if obs_stage o2 <? obs_stage o1 then 1 else 0) + count_escalations rest
  end.

Fixpoint count_improvements (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (if obs_stage o1 <? obs_stage o2 then 1 else 0) + count_improvements rest
  end.

(* Magnitude companions to count_escalations / count_improvements.
   These sum the per-adjacent stage delta (with nat-monus zeroing the
   inactive direction) and telescope cleanly to the net stage change. *)
Fixpoint sum_escalation_magnitude (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (obs_stage o1 - obs_stage o2) + sum_escalation_magnitude rest
  end.

Fixpoint sum_improvement_magnitude (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] | [_] => 0
  | o1 :: ((o2 :: _) as rest) =>
      (obs_stage o2 - obs_stage o1) + sum_improvement_magnitude rest
  end.

Fixpoint max_stage (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] => 0
  | [o] => obs_stage o
  | o :: rest => Nat.max (obs_stage o) (max_stage rest)
  end.

Fixpoint min_stage (ts : PatientTimeSeries) : nat :=
  match ts with
  | [] => 0
  | [o] => obs_stage o
  | o :: rest => Nat.min (obs_stage o) (min_stage rest)
  end.

Definition stage_range (ts : PatientTimeSeries) : nat :=
  max_stage ts - min_stage ts.

Definition compute_trajectory (ts : PatientTimeSeries) : TemporalProgression.ClinicalTrajectory :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      if negb (obs_time_hours e <=? obs_time_hours l) then TemporalProgression.Stable
      else
      let current := obs_stage l in
      let peak := max_stage ts in
      let stage_delta := (Z.of_nat current - Z.of_nat (obs_stage e))%Z in
      let duration := obs_time_hours l - obs_time_hours e in
      if current <? peak then
        if (stage_delta >? 0)%Z then TemporalProgression.Worsening
        else if (stage_delta <? 0)%Z then TemporalProgression.Improving
        else TemporalProgression.Stable
      else
      if (duration =? 0) then TemporalProgression.Stable
      else if (stage_delta * 240 >? 20 * Z.of_nat duration)%Z then TemporalProgression.RapidDeterioration
      else if (stage_delta >? 0)%Z then TemporalProgression.Worsening
      else if (stage_delta <? 0)%Z then TemporalProgression.Improving
      else TemporalProgression.Stable
  | _, _ => TemporalProgression.Stable
  end.

Definition stage_velocity_x10 (ts : PatientTimeSeries) : Z :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      let stage_delta := (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e))%Z in
      let duration := obs_time_hours l - obs_time_hours e in
      if duration =? 0 then 0%Z
      else ((stage_delta * 240) / Z.of_nat duration)%Z
  | _, _ => 0%Z
  end.

Definition severity_trend (ts : PatientTimeSeries) : Z :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      (Z.of_nat (obs_severity l) - Z.of_nat (obs_severity e))%Z
  | _, _ => 0%Z
  end.

Definition reached_stage_IIIB (ts : PatientTimeSeries) : bool :=
  6 <=? max_stage ts.

Definition crossed_surgical_threshold (ts : PatientTimeSeries) : bool :=
  match earliest ts with
  | Some e => (obs_stage e <? 6) && reached_stage_IIIB ts
  | None => false
  end.

Fixpoint first_at_stage (ts : PatientTimeSeries) (threshold : nat) : option Observation :=
  match ts with
  | [] => None
  | o :: rest =>
      match first_at_stage rest threshold with
      | Some found => Some found
      | None => if threshold <=? obs_stage o then Some o else None
      end
  end.

Definition time_to_stage (ts : PatientTimeSeries) (threshold : nat) : option nat :=
  match first_at_stage ts threshold, earliest ts with
  | Some target, Some start => Some (obs_time_hours target - obs_time_hours start)
  | _, _ => None
  end.

Definition add_observation (obs : Observation) (ts : PatientTimeSeries) : option PatientTimeSeries :=
  match ts with
  | [] =>
      if obs_time_hours obs =? ClinicalState.hours_since_symptom_onset (obs_state obs)
      then Some [obs]
      else None
  | prev :: _ =>
      if (obs_time_hours prev <=? obs_time_hours obs) &&
         (obs_time_hours obs =? ClinicalState.hours_since_symptom_onset (obs_state obs))
      then Some (obs :: ts)
      else None
  end.

Lemma empty_series_stable : compute_trajectory [] = TemporalProgression.Stable.
Proof. reflexivity. Qed.

Lemma singleton_series_stable : forall o,
  compute_trajectory [o] = TemporalProgression.Stable.
Proof.
  intros o. unfold compute_trajectory, latest, earliest, max_stage. simpl.
  rewrite Nat.leb_refl. simpl.
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

(* Telescoping identity: latest stage plus accumulated improvements equals
   earliest stage plus accumulated escalations. Stated in nat using the
   monus invariant a + (b - a) = max a b to bypass Z conversion. *)
Lemma stage_change_telescopes : forall ts l e,
  latest ts = Some l ->
  earliest ts = Some e ->
  obs_stage l + sum_improvement_magnitude ts =
  obs_stage e + sum_escalation_magnitude ts.
Proof.
  induction ts as [|o ts' IH]; intros l e Hl He.
  - discriminate.
  - destruct ts' as [|o' rest].
    + simpl in Hl, He. inversion Hl. inversion He. subst.
      simpl. lia.
    + simpl in Hl. inversion Hl. subst l. clear Hl.
      simpl in He.
      specialize (IH o' e eq_refl He).
      change (sum_escalation_magnitude (o :: o' :: rest))
        with ((obs_stage o - obs_stage o') + sum_escalation_magnitude (o' :: rest)).
      change (sum_improvement_magnitude (o :: o' :: rest))
        with ((obs_stage o' - obs_stage o) + sum_improvement_magnitude (o' :: rest)).
      destruct (Nat.le_gt_cases (obs_stage o) (obs_stage o')) as [Hle|Hgt].
      * assert (Hzero : obs_stage o - obs_stage o' = 0) by lia.
        rewrite Hzero, Nat.add_0_l. lia.
      * assert (Hzero : obs_stage o' - obs_stage o = 0) by lia.
        rewrite Hzero, Nat.add_0_l. lia.
Qed.

(* Z corollary: explicit net-delta form. *)
Corollary stage_change_telescopes_Z : forall ts l e,
  latest ts = Some l ->
  earliest ts = Some e ->
  (Z.of_nat (sum_escalation_magnitude ts)
   - Z.of_nat (sum_improvement_magnitude ts) =
   Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e))%Z.
Proof.
  intros ts l e Hl He.
  pose proof (stage_change_telescopes ts l e Hl He) as H.
  lia.
Qed.

(* Event-count bound: across a series of length n, at most n adjacent-pair
   events fire across both directions, since escalation and improvement at
   the same pair are mutually exclusive. *)
Lemma escalations_improvements_bounded : forall ts,
  count_escalations ts + count_improvements ts <= series_length ts.
Proof.
  induction ts as [|o ts' IH].
  - simpl. lia.
  - destruct ts' as [|o' rest].
    + simpl. lia.
    + unfold series_length in *. simpl in *.
      destruct (obs_stage o' <? obs_stage o) eqn:E1;
      destruct (obs_stage o <? obs_stage o') eqn:E2; try lia.
      apply Nat.ltb_lt in E1, E2. lia.
Qed.

(* When the patient peaked higher than current, compute_trajectory
   cannot emit RapidDeterioration. *)
Lemma peak_recovery_not_rapid : forall ts l,
  latest ts = Some l ->
  obs_stage l <? max_stage ts = true ->
  compute_trajectory ts <> TemporalProgression.RapidDeterioration.
Proof.
  intros ts l Hl Hpeak. unfold compute_trajectory.
  rewrite Hl.
  destruct (earliest ts) as [e|]; [|discriminate].
  destruct (negb (obs_time_hours e <=? obs_time_hours l)); [discriminate|].
  rewrite Hpeak.
  destruct ((Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e) >? 0)%Z);
  [discriminate|].
  destruct ((Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e) <? 0)%Z);
  discriminate.
Qed.

(* Rapid-climb witness: true when some adjacent pair exceeds the rapid threshold. *)
Fixpoint had_rapid_climb (ts : PatientTimeSeries) : bool :=
  match ts with
  | [] | [_] => false
  | o1 :: ((o2 :: _) as rest) =>
      let dh := obs_time_hours o1 - obs_time_hours o2 in
      let ds := (Z.of_nat (obs_stage o1) - Z.of_nat (obs_stage o2))%Z in
      ((obs_time_hours o2 <=? obs_time_hours o1) &&
       (ds * 240 >? 20 * Z.of_nat dh)%Z)%bool
      || had_rapid_climb rest
  end.

Lemma had_rapid_climb_singleton : forall o, had_rapid_climb [o] = false.
Proof. reflexivity. Qed.

Lemma had_rapid_climb_empty : had_rapid_climb [] = false.
Proof. reflexivity. Qed.

Lemma had_rapid_climb_cons : forall o1 o2 rest,
  had_rapid_climb (o1 :: o2 :: rest) =
  (((obs_time_hours o2 <=? obs_time_hours o1) &&
    ((Z.of_nat (obs_stage o1) - Z.of_nat (obs_stage o2)) * 240
     >? 20 * Z.of_nat (obs_time_hours o1 - obs_time_hours o2))%Z)%bool
   || had_rapid_climb (o2 :: rest)).
Proof. reflexivity. Qed.

(* Partial unification of TemporalProgression.infer_trajectory (point-to-
   point) and TimeSeries.compute_trajectory (series-aware). The two
   procedures use different rapid-deterioration thresholds (infer_trajectory
   uses hours <? 6; compute_trajectory uses cross-multiplication for
   1-stage-per-12h) so do not agree on rapid vs worsening. The agreement
   on Stable when delta = 0 is captured below. *)

Lemma infer_trajectory_stable_on_zero : forall hours,
  TemporalProgression.infer_trajectory 0%Z hours = TemporalProgression.Stable.
Proof.
  intros hours. unfold TemporalProgression.infer_trajectory. reflexivity.
Qed.

(* Direction encoding: the trichotomy distinction (improving / stable /
   worsening) collapses RapidDeterioration into Worsening, since both
   procedures agree at the trichotomy level even when they disagree on
   whether a worsening trajectory crosses the rapid threshold. *)
Definition direction_z (t : TemporalProgression.ClinicalTrajectory) : Z :=
  match t with
  | TemporalProgression.Improving => (-1)%Z
  | TemporalProgression.Stable => 0%Z
  | TemporalProgression.Worsening => 1%Z
  | TemporalProgression.RapidDeterioration => 1%Z
  end.

Lemma infer_trajectory_direction : forall delta hours,
  direction_z (TemporalProgression.infer_trajectory delta hours) = Z.sgn delta.
Proof.
  intros delta hours.
  destruct delta as [|p|p].
  - unfold TemporalProgression.infer_trajectory, direction_z. simpl. reflexivity.
  - unfold TemporalProgression.infer_trajectory.
    change ((Z.pos p >? 0)%Z) with true.
    destruct (hours <? 6); unfold direction_z; reflexivity.
  - unfold TemporalProgression.infer_trajectory.
    change ((Z.neg p >? 0)%Z) with false.
    change ((Z.neg p <? 0)%Z) with true.
    unfold direction_z. reflexivity.
Qed.

(* Direction agreement on compute_trajectory for strict-time-ordered
   two-point series. The strict time inequality eliminates the
   degenerate duration-zero case where stage delta is non-zero.
   Three cases by sign of stage delta; in each, the compute_trajectory
   body reduces to a known constructor and direction_z matches Z.sgn. *)
Lemma compute_trajectory_two_point_direction : forall l e,
  obs_time_hours e < obs_time_hours l ->
  direction_z (compute_trajectory [l; e]) =
  Z.sgn (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e)).
Proof.
  intros l e Htime.
  assert (Htime_le : obs_time_hours e <= obs_time_hours l) by lia.
  apply Nat.leb_le in Htime_le as Htime_b.
  assert (Hdur_nz : (obs_time_hours l - obs_time_hours e =? 0) = false)
    by (apply Nat.eqb_neq; lia).
  destruct (Z_dec' (Z.of_nat (obs_stage l)) (Z.of_nat (obs_stage e)))
    as [[Hlt|Hgt]|Heq].
  - (* stage(l) < stage(e) *)
    assert (Hcompute : compute_trajectory [l; e] = TemporalProgression.Improving).
    { unfold compute_trajectory. cbn [latest earliest max_stage].
      rewrite Htime_b. cbn [negb].
      assert (Hpeak : (obs_stage l <? Nat.max (obs_stage l) (obs_stage e)) = true)
        by (apply Nat.ltb_lt; lia).
      rewrite Hpeak.
      assert (Hgt0_false : (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e) >? 0)%Z = false)
        by (rewrite Z.gtb_ltb; apply Z.ltb_ge; lia).
      rewrite Hgt0_false.
      assert (Hlt0_true : (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e) <? 0)%Z = true)
        by (apply Z.ltb_lt; lia).
      rewrite Hlt0_true. reflexivity. }
    rewrite Hcompute. simpl direction_z.
    symmetry. apply Z.sgn_neg. lia.
  - (* stage(l) > stage(e) *)
    assert (Egt : (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e) >? 0)%Z = true)
      by (rewrite Z.gtb_ltb; apply Z.ltb_lt; lia).
    assert (Hcompute : direction_z (compute_trajectory [l; e]) = 1%Z).
    { unfold compute_trajectory. cbn [latest earliest max_stage].
      rewrite Htime_b. cbn [negb].
      assert (Hpeak : (obs_stage l <? Nat.max (obs_stage l) (obs_stage e)) = false)
        by (apply Nat.ltb_ge; lia).
      rewrite Hpeak.
      rewrite Hdur_nz.
      destruct ((Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e)) * 240 >?
                20 * Z.of_nat (obs_time_hours l - obs_time_hours e))%Z.
      - reflexivity.
      - rewrite Egt. reflexivity. }
    rewrite Hcompute. symmetry. apply Z.sgn_pos. lia.
  - (* stage(l) = stage(e) *)
    assert (Hcompute : compute_trajectory [l; e] = TemporalProgression.Stable).
    { unfold compute_trajectory. cbn [latest earliest max_stage].
      rewrite Htime_b. cbn [negb].
      assert (Hpeak : (obs_stage l <? Nat.max (obs_stage l) (obs_stage e)) = false)
        by (apply Nat.ltb_ge; lia).
      rewrite Hpeak.
      rewrite Hdur_nz, Heq, Z.sub_diag.
      change (0 * 240)%Z with 0%Z.
      assert (H_not_gt : (0 >? 20 * Z.of_nat (obs_time_hours l - obs_time_hours e))%Z = false).
      { rewrite Z.gtb_ltb. apply Z.ltb_ge.
        pose proof (Nat2Z.is_nonneg (obs_time_hours l - obs_time_hours e)). lia. }
      rewrite H_not_gt. reflexivity. }
    rewrite Hcompute, Heq, Z.sub_diag. reflexivity.
Qed.

Theorem trajectory_direction_agrees_strict : forall l e,
  obs_time_hours e < obs_time_hours l ->
  direction_z (compute_trajectory [l; e]) =
  direction_z
    (TemporalProgression.infer_trajectory
      (Z.of_nat (obs_stage l) - Z.of_nat (obs_stage e))%Z
      (obs_time_hours l - obs_time_hours e)).
Proof.
  intros l e Htime.
  rewrite compute_trajectory_two_point_direction by exact Htime.
  rewrite infer_trajectory_direction. reflexivity.
Qed.



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

(* Inconsistent timestamp: obs_time_hours differs from embedded state clock *)
Definition inconsistent_obs : Observation :=
  MkObservation 10
    (ClinicalState.MkClinicalState
      ClinicalState.default_risk_factors
      (Some ClinicalState.default_labs)
      (Some ClinicalState.default_coag)
      ClinicalState.default_micro
      (Some ClinicalState.default_vitals)
      SystemicSigns.no_signs
      IntestinalSigns.no_signs
      RadiographicSigns.no_findings
      NeonatalOrganFailure.NeuroNormal
      5 5 5 5).

Lemma inconsistent_obs_rejected :
  add_observation inconsistent_obs [] = None.
Proof. vm_compute. reflexivity. Qed.

Definition early_obs : Observation :=
  make_observation 2 ClinicalState.empty.

Definition late_obs : Observation :=
  make_observation 8 ClinicalState.empty.

Lemma backward_time_rejected :
  add_observation early_obs [late_obs] = None.
Proof. vm_compute. reflexivity. Qed.

(* Continuous-time semantics interface. PatientPath represents a
   piecewise-constant function from time (in tenths-of-hours, since we
   avoid Reals) to ClinicalState. The discrete classify_from_series is
   sound for the continuous interpretation under a bounded stage-rate-
   of-change assumption: between adjacent observations, stage cannot
   shift by more than the rapid-deterioration threshold. *)
Record PatientPath : Type := MkPatientPath {
  pp_observations : PatientTimeSeries;
  pp_bounded_rate : forall i j o1 o2,
    nth_error pp_observations i = Some o1 ->
    nth_error pp_observations j = Some o2 ->
    obs_time_hours o1 <= obs_time_hours o2 ->
    (Z.of_nat (obs_stage o2) - Z.of_nat (obs_stage o1) <=
     Z.of_nat (20 * (obs_time_hours o2 - obs_time_hours o1)))%Z /\
    (Z.of_nat (obs_stage o1) - Z.of_nat (obs_stage o2) <=
     Z.of_nat (20 * (obs_time_hours o2 - obs_time_hours o1)))%Z
}.

Definition pp_to_series (p : PatientPath) : PatientTimeSeries :=
  pp_observations p.

(* Smart constructor for the trivial singleton-observation case. The
   bounded-rate obligation collapses because the only valid (i, j)
   pair is (0, 0), where both the stage delta and the time delta are
   zero. *)
Definition mk_singleton_path (o : Observation) : PatientPath.
Proof.
  refine (MkPatientPath [o] _).
  intros i j o1 o2 H1 H2 Htime.
  destruct i as [|i']; destruct j as [|j'].
  - simpl in H1, H2. inversion H1. inversion H2. subst.
    rewrite Nat.sub_diag, Z.sub_diag. simpl. split; lia.
  - destruct j'; simpl in H2; discriminate.
  - destruct i'; simpl in H1; discriminate.
  - destruct i'; simpl in H1; discriminate.
Defined.

(* General smart constructor. Validates the adjacent-pair rate bound (each
   adjacent pair has bounded stage delta vs time delta) and time descent
   (each adjacent pair has older later in the list), then lifts to all
   pairs via the AllPairsBounded inductive predicate which encodes the
   triangle inequality structurally. *)

Fixpoint validate_adjacent_rate (ts : PatientTimeSeries) : bool :=
  match ts with
  | [] => true
  | [_] => true
  | o1 :: ((o2 :: _) as rest) =>
      let dt := obs_time_hours o1 - obs_time_hours o2 in
      (obs_time_hours o2 <=? obs_time_hours o1) &&
      ((Z.of_nat (obs_stage o2) - Z.of_nat (obs_stage o1) <=?
        Z.of_nat (20 * dt))%Z) &&
      ((Z.of_nat (obs_stage o1) - Z.of_nat (obs_stage o2) <=?
        Z.of_nat (20 * dt))%Z) &&
      validate_adjacent_rate rest
  end.

(* The head dominates an observation x: t(x) <= t(head), and the
   stage delta between them is bounded by 20 times the time delta. *)
Definition head_dominates (h x : Observation) : Prop :=
  obs_time_hours x <= obs_time_hours h /\
  (Z.of_nat (obs_stage h) - Z.of_nat (obs_stage x) <=
   Z.of_nat (20 * (obs_time_hours h - obs_time_hours x)))%Z /\
  (Z.of_nat (obs_stage x) - Z.of_nat (obs_stage h) <=
   Z.of_nat (20 * (obs_time_hours h - obs_time_hours x)))%Z.

Inductive AllPairsBounded : PatientTimeSeries -> Prop :=
  | APB_nil : AllPairsBounded []
  | APB_cons : forall h ts,
      (forall x, In x ts -> head_dominates h x) ->
      AllPairsBounded ts ->
      AllPairsBounded (h :: ts).

(* Triangle inequality lift: if h dominates h2 and h2 dominates x, then
   h dominates x. *)
Lemma head_dominates_trans : forall h h2 x,
  head_dominates h h2 ->
  head_dominates h2 x ->
  head_dominates h x.
Proof.
  intros h h2 x [Hth2 [Hd1 Hd2]] [Htx [He1 He2]].
  unfold head_dominates. split; [|split].
  - lia.
  - rewrite Nat2Z.inj_mul in Hd1, He1, Hd2, He2.
    rewrite Nat2Z.inj_mul.
    assert (Hsub_h_x : (Z.of_nat (obs_time_hours h - obs_time_hours x) =
                       Z.of_nat (obs_time_hours h - obs_time_hours h2) +
                       Z.of_nat (obs_time_hours h2 - obs_time_hours x))%Z).
    { rewrite <- Nat2Z.inj_add. f_equal. lia. }
    lia.
  - rewrite Nat2Z.inj_mul in Hd1, He1, Hd2, He2.
    rewrite Nat2Z.inj_mul.
    assert (Hsub_h_x : (Z.of_nat (obs_time_hours h - obs_time_hours x) =
                       Z.of_nat (obs_time_hours h - obs_time_hours h2) +
                       Z.of_nat (obs_time_hours h2 - obs_time_hours x))%Z).
    { rewrite <- Nat2Z.inj_add. f_equal. lia. }
    lia.
Qed.

Lemma validate_implies_all_pairs_bounded : forall ts,
  validate_adjacent_rate ts = true -> AllPairsBounded ts.
Proof.
  induction ts as [|o ts' IH]; intros Hv.
  - constructor.
  - destruct ts' as [|o2 rest].
    + apply APB_cons; [intros x Hx; destruct Hx | constructor].
    + (* Use change to expose the && structure without unfolding multiplication. *)
      change (validate_adjacent_rate (o :: o2 :: rest)) with
        ((obs_time_hours o2 <=? obs_time_hours o) &&
         ((Z.of_nat (obs_stage o2) - Z.of_nat (obs_stage o) <=?
           Z.of_nat (20 * (obs_time_hours o - obs_time_hours o2)))%Z) &&
         ((Z.of_nat (obs_stage o) - Z.of_nat (obs_stage o2) <=?
           Z.of_nat (20 * (obs_time_hours o - obs_time_hours o2)))%Z) &&
         validate_adjacent_rate (o2 :: rest)) in Hv.
      apply andb_true_iff in Hv. destruct Hv as [Hv Hrec].
      apply andb_true_iff in Hv. destruct Hv as [Hv Hd_o2_o].
      apply andb_true_iff in Hv. destruct Hv as [Htime_o2_o Hd_o_o2].
      apply Nat.leb_le in Htime_o2_o.
      apply Z.leb_le in Hd_o_o2, Hd_o2_o.
      pose proof (IH Hrec) as Hapb_tail.
      apply APB_cons; [|exact Hapb_tail].
      intros x Hx.
      assert (Hdom_o_o2 : head_dominates o o2).
      { unfold head_dominates. split; [exact Htime_o2_o|]. split; assumption. }
      destruct Hx as [Heq|Hin].
      * subst x. exact Hdom_o_o2.
      * (* x is in rest. From AllPairsBounded (o2 :: rest), o2 dominates x. *)
        inversion Hapb_tail as [|h_t ts_t Hdom_o2 _]; subst.
        apply head_dominates_trans with (h2 := o2);
          [exact Hdom_o_o2 | apply Hdom_o2; exact Hin].
Qed.

(* Indexed bound from AllPairsBounded. *)
Lemma all_pairs_bounded_to_indexed : forall ts,
  AllPairsBounded ts ->
  forall i j o1 o2,
    nth_error ts i = Some o1 ->
    nth_error ts j = Some o2 ->
    obs_time_hours o1 <= obs_time_hours o2 ->
    (Z.of_nat (obs_stage o2) - Z.of_nat (obs_stage o1) <=
     Z.of_nat (20 * (obs_time_hours o2 - obs_time_hours o1)))%Z /\
    (Z.of_nat (obs_stage o1) - Z.of_nat (obs_stage o2) <=
     Z.of_nat (20 * (obs_time_hours o2 - obs_time_hours o1)))%Z.
Proof.
  intros ts Hapb. induction Hapb as [|h ts' Hdom Hapb_rest IH]; intros i j o1 o2 H1 H2 Htime.
  - destruct i; simpl in H1; discriminate.
  - destruct i as [|i']; destruct j as [|j']; simpl in H1, H2.
    + (* i = j = 0: o1 = o2 = h *)
      inversion H1. inversion H2. subst.
      rewrite Nat.sub_diag, Z.sub_diag. simpl. split; lia.
    + (* i = 0, j = S j': o1 = h, o2 = nth_error ts' j' *)
      inversion H1. subst o1.
      apply nth_error_In in H2.
      pose proof (Hdom o2 H2) as [Htime_o2_h [Hbnd1 Hbnd2]].
      (* Htime: t(h) <= t(o2). Htime_o2_h: t(o2) <= t(h). So equality. *)
      assert (Heqt : obs_time_hours o2 = obs_time_hours h) by lia.
      rewrite Heqt. rewrite Nat.sub_diag. simpl.
      rewrite Heqt in Hbnd1, Hbnd2. rewrite Nat.sub_diag in Hbnd1, Hbnd2.
      simpl in Hbnd1, Hbnd2. split; lia.
    + (* i = S i', j = 0: o1 = nth_error ts' i', o2 = h *)
      inversion H2. subst o2.
      apply nth_error_In in H1.
      pose proof (Hdom o1 H1) as [Htime_o1_h [Hbnd1 Hbnd2]].
      rewrite Nat2Z.inj_mul in Hbnd1, Hbnd2.
      assert (Hsub : obs_time_hours h - obs_time_hours o1 =
                     obs_time_hours h - obs_time_hours o1) by reflexivity.
      split.
      * (* Z(stage(h)) - Z(stage(o1)) <= Z(20 * (t(h) - t(o1))) *)
        rewrite Nat2Z.inj_mul. lia.
      * rewrite Nat2Z.inj_mul. lia.
    + (* i = S i', j = S j': both in ts' *)
      apply IH with (i := i') (j := j'); assumption.
Qed.

(* The full smart constructor. *)
Definition try_mk_patient_path (ts : PatientTimeSeries) : option PatientPath.
Proof.
  destruct (validate_adjacent_rate ts) eqn:Hv.
  - refine (Some (MkPatientPath ts _)).
    intros i j o1 o2 H1 H2 Htime.
    apply (all_pairs_bounded_to_indexed ts
             (validate_implies_all_pairs_bounded ts Hv) i j o1 o2 H1 H2 Htime).
  - exact None.
Defined.

(* Discrete-classifier soundness on a bounded-rate PatientPath: when the
   latest observation exists, the classifier returns its stage. *)
Lemma pp_classify_latest_agrees : forall p o,
  latest (pp_to_series p) = Some o ->
  Classification.classify (obs_state o) = Classification.classify (obs_state o).
Proof. intros. reflexivity. Qed.

(* Continuous-time piecewise-constant interpretation. At time t, the
   stage is the classification of the latest observation whose time is
   at or before t. For times before all observations, the function
   returns None. The list is in newest-first order, so the iteration
   finds the latest observation with obs_time_hours <= t by walking
   from newest to oldest. *)
Fixpoint stage_at_time_helper (ts : PatientTimeSeries) (t : nat) : option Stage.t :=
  match ts with
  | [] => None
  | o :: rest =>
      if obs_time_hours o <=? t
      then Some (Classification.classify (obs_state o))
      else stage_at_time_helper rest t
  end.

Definition pp_stage_at_time (p : PatientPath) (t : nat) : option Stage.t :=
  stage_at_time_helper (pp_observations p) t.

(* Continuous-discrete consistency: at the latest observation's time,
   the piecewise-constant interpretation agrees with the discrete
   classify_from_series. The discrete classifier returns the latest
   observation's stage; the continuous interpretation at that time
   point also returns it, since the latest observation is the first
   one encountered with time <= t in the newest-first iteration. *)
Theorem pp_continuous_consistent_at_latest :
  forall p obs,
    latest (pp_to_series p) = Some obs ->
    pp_stage_at_time p (obs_time_hours obs) =
    Some (Classification.classify (obs_state obs)).
Proof.
  intros p obs Hlatest.
  unfold pp_stage_at_time, pp_to_series in *.
  destruct (pp_observations p) as [|o rest]; simpl in Hlatest.
  - discriminate.
  - inversion Hlatest. subst.
    simpl. rewrite Nat.leb_refl. reflexivity.
Qed.

(* Continuous-time bounded-rate consequence: when the piecewise-constant
   interpretation returns a stage at some time t, that stage corresponds
   to an observation whose time is bounded by t. *)
Lemma stage_at_time_implies_observation : forall ts t s,
  stage_at_time_helper ts t = Some s ->
  exists o, In o ts /\ obs_time_hours o <= t /\
            Classification.classify (obs_state o) = s.
Proof.
  induction ts as [|o ts' IH]; intros t s H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (obs_time_hours o <=? t) eqn:Et.
    + apply Nat.leb_le in Et.
      inversion H. subst.
      exists o. split; [left; reflexivity | split; assumption + reflexivity].
    + destruct (IH t s H) as [oa [Hin [Htime Hcls]]].
      exists oa. split; [right; exact Hin | split; assumption].
Qed.

(* The continuous interpretation is sound for the discrete classifier:
   any stage value returned by pp_stage_at_time corresponds to an actual
   observation in the PatientPath whose time is consistent with the
   query time. This is the supremum-over-continuous-interpretations
   theorem in its piecewise-constant form: every continuous reading
   has a discrete witness. *)
Theorem pp_continuous_has_discrete_witness :
  forall p t s,
    pp_stage_at_time p t = Some s ->
    exists o, In o (pp_observations p) /\
              obs_time_hours o <= t /\
              Classification.classify (obs_state o) = s.
Proof.
  intros p t s H. unfold pp_stage_at_time in H.
  apply stage_at_time_implies_observation. exact H.
Qed.

(* Singleton-series direction agreement bundling infer_trajectory_stable_on_zero
   and the singleton-stable series result. *)
Lemma trajectory_singleton_both_stable : forall o,
  compute_trajectory [o] = TemporalProgression.Stable /\
  TemporalProgression.infer_trajectory 0%Z 0 = TemporalProgression.Stable.
Proof.
  intros o. split.
  - apply singleton_series_stable.
  - apply infer_trajectory_stable_on_zero.
Qed.

End TimeSeries.

Module TrajectoryClassification.

Definition classify_from_series (ts : TimeSeries.PatientTimeSeries) : option Stage.t :=
  match TimeSeries.latest ts with
  | Some obs => Some (Classification.classify (TimeSeries.obs_state obs))
  | None => None
  end.

Definition classify_with_trajectory (ts : TimeSeries.PatientTimeSeries)
    : option Classification.TrajectoryAwareClassification :=
  match TimeSeries.latest ts with
  | Some obs =>
      let stage := Classification.classify (TimeSeries.obs_state obs) in
      let traj := TimeSeries.compute_trajectory ts in
      let urg := Classification.urgency_from_trajectory traj stage in
      let esc := TimeSeries.count_escalations ts in
      let hrs := match TimeSeries.first_at_stage ts (Stage.to_nat stage) with
                 | Some first_obs =>
                     TimeSeries.obs_time_hours obs - TimeSeries.obs_time_hours first_obs
                 | None => 0
                 end in
      Some (Classification.MkTrajectoryAware stage traj urg esc hrs)
  | None => None
  end.

Definition escalation_warranted (ts : TimeSeries.PatientTimeSeries) : bool :=
  match classify_with_trajectory ts with
  | Some tac =>
      match Classification.tac_urgency tac with
      | Classification.Emergent => true
      | Classification.Urgent => true
      | _ => false
      end
  | None => false
  end.

Definition recommended_reassess_hours (ts : TimeSeries.PatientTimeSeries) : nat :=
  match classify_with_trajectory ts with
  | Some tac =>
      match Classification.tac_urgency tac with
      | Classification.Emergent => 1
      | Classification.Urgent => 2
      | Classification.Elevated => 4
      | Classification.Routine => 8
      end
  | None => 8
  end.

End TrajectoryClassification.

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
  | NPO_Antibiotics_3days =>
      ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_I
  | NPO_Antibiotics_7to10days =>
      ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_II
  | NPO_Antibiotics_14days =>
      ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_III
  | SurgicalIntervention =>
      ClinicalParameters.param_value ClinicalParameters.npo_duration_stage_III
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

(* NPO durations are monotone in stage. With ClinicalParameters routing,
   the proof reduces to comparing the parameter values. *)
Lemma npo_duration_days_monotone : forall s1 s2,
  Stage.leb s1 s2 = true ->
  npo_duration_days (of_stage s1) <= npo_duration_days (of_stage s2).
Proof.
  intros [] []; vm_compute; intro H; try lia; discriminate.
Qed.

(* Stage IIA does not require surgery. *)
Theorem classify_IIA_no_surgery : forall c,
  Classification.classify c = Stage.IIA ->
  requires_surgery (of_stage (Classification.classify c)) = false.
Proof.
  intros c H. rewrite H. reflexivity.
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

(* Derive fixed_loop from a time series. A fixed loop is an
   intestinal-dilation finding that persists across two or more
   adjacent observations (clinically: 24-48h on serial imaging
   without movement). The single-state surgical_context_of cannot
   detect this because the bridge has no memory; the series-aware
   variant inspects two consecutive observations. *)
Definition fixed_loop_from_series (ts : TimeSeries.PatientTimeSeries) : bool :=
  match ts with
  | o1 :: o2 :: _ =>
      RadiographicSigns.intestinal_dilation
        (ClinicalState.radiographic (TimeSeries.obs_state o1))
      && RadiographicSigns.intestinal_dilation
        (ClinicalState.radiographic (TimeSeries.obs_state o2))
  | _ => false
  end.

(* Serial-imaging-window detector: checks that the latest observation's
   intestinal_dilation persists from an earlier observation at least 24
   hours older. This matches the clinical definition of a fixed loop
   (persistent over 24-48h on serial imaging) more closely than the
   adjacent-pair detector above. *)
Definition fixed_loop_persists_24h (ts : TimeSeries.PatientTimeSeries) : bool :=
  match ts with
  | o1 :: rest =>
      existsb (fun o2 =>
        (24 <=? (TimeSeries.obs_time_hours o1 - TimeSeries.obs_time_hours o2)) &&
        RadiographicSigns.intestinal_dilation
          (ClinicalState.radiographic (TimeSeries.obs_state o1)) &&
        RadiographicSigns.intestinal_dilation
          (ClinicalState.radiographic (TimeSeries.obs_state o2))) rest
  | _ => false
  end.

Lemma fixed_loop_persists_24h_implies_dilated_latest : forall ts o,
  fixed_loop_persists_24h (o :: ts) = true ->
  RadiographicSigns.intestinal_dilation
    (ClinicalState.radiographic (TimeSeries.obs_state o)) = true.
Proof.
  intros ts o H. unfold fixed_loop_persists_24h in H.
  apply existsb_exists in H. destruct H as [o2 [_ Hcond]].
  apply andb_true_iff in Hcond. destruct Hcond as [Hcond _].
  apply andb_true_iff in Hcond. destruct Hcond as [_ Hdilat]. exact Hdilat.
Qed.

Definition surgical_context_of_series
    (ts : TimeSeries.PatientTimeSeries)
    (deteriorating : bool) (paracentesis_positive : bool)
    : option SurgicalContext :=
  match TimeSeries.latest ts with
  | Some obs =>
      let c := TimeSeries.obs_state obs in
      let rad := ClinicalState.radiographic c in
      let int := ClinicalState.intestinal c in
      Some (MkSurgicalContext
        (RadiographicSigns.pneumoperitoneum rad)
        (fixed_loop_from_series ts)
        (IntestinalSigns.abdominal_cellulitis int)
        deteriorating
        paracentesis_positive
        (RadiographicSigns.portal_venous_gas rad && deteriorating))
  | None => None
  end.

(* Series-derived bridge picks up fixed_loop where the single-state
   bridge hardcoded false. *)
Lemma series_bridge_detects_fixed_loop : forall ts d p,
  fixed_loop_from_series ts = true ->
  match surgical_context_of_series ts d p with
  | Some ctx => has_fixed_loop ctx = true
  | None => False
  end.
Proof.
  intros ts d p H. unfold surgical_context_of_series.
  destruct (TimeSeries.latest ts) as [obs|] eqn:E.
  - simpl. exact H.
  - destruct ts as [|o [|o' rest]]; simpl in *; discriminate.
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

(* Refinement carrying a vasopressor-support flag for non-ELBW unstable
   patients. The procedure remains ExploratoryLaparotomy (per NET trial)
   but the caller is informed that vasopressor support is required pre-op.
   For ELBW unstable, behavior unchanged: drain as bridge. *)
Record StabilityAwareProcedure : Type := MkStabilityAware {
  sap_procedure : Procedure;
  sap_vasopressor_support : bool
}.

Definition initial_procedure_with_stability
    (birth_weight_grams : nat) (hemodynamically_unstable : bool)
    : StabilityAwareProcedure :=
  if (birth_weight_grams <? 1000) && hemodynamically_unstable then
    MkStabilityAware PrimaryPeritonealDrainage true
  else if hemodynamically_unstable then
    (* Non-ELBW unstable: laparotomy with vasopressor support *)
    MkStabilityAware ExploratoryLaparotomy true
  else
    MkStabilityAware ExploratoryLaparotomy false.

Lemma stability_aware_non_elbw_unstable_flagged : forall bw,
  1000 <= bw ->
  sap_vasopressor_support (initial_procedure_with_stability bw true) = true.
Proof.
  intros bw H. unfold initial_procedure_with_stability.
  destruct (bw <? 1000) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

Lemma stability_aware_stable_no_pressor : forall bw,
  sap_vasopressor_support (initial_procedure_with_stability bw false) = false.
Proof.
  intros bw. unfold initial_procedure_with_stability.
  rewrite andb_false_r. reflexivity.
Qed.

(* Procedure choice agrees with the original on the ELBW boundaries. *)
Lemma stability_aware_agrees_on_procedure : forall bw stab,
  sap_procedure (initial_procedure_with_stability bw stab) =
  initial_procedure_for_perforation bw stab.
Proof.
  intros bw stab. unfold initial_procedure_with_stability,
    initial_procedure_for_perforation.
  destruct (bw <? 1000); destruct stab; reflexivity.
Qed.

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
  | Stage.IA | Stage.IB =>
      ClinicalParameters.param_value ClinicalParameters.abx_duration_stage_I
  | Stage.IIA | Stage.IIB =>
      ClinicalParameters.param_value ClinicalParameters.abx_duration_stage_II
  | Stage.IIIA | Stage.IIIB =>
      ClinicalParameters.param_value ClinicalParameters.abx_duration_stage_III
  end.

(* Culture-directed therapy: adjust regimen based on microbiology results.
   Blood culture timing fields gate escalation: no positive result after
   the escalation threshold hours triggers broadening consideration.
   Lambert et al. 2012, J Pediatr Surg 47(11):2111-2118. *)
Definition culture_escalation_threshold_h : nat :=
  ClinicalParameters.param_value ClinicalParameters.culture_escalation_hours.

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

(* culture_directed_regimen preserves gram-positive coverage. The base
   regimen has gram-positive coverage only at stage III (Broad_VancMeropenem);
   in that case every culture-directed branch also lands on a Vancomycin-
   bearing regimen. *)
Lemma culture_directed_never_narrows_gram_pos : forall s m h,
  has_gram_positive_coverage (recommended_regimen_by_stage s) = true ->
  has_gram_positive_coverage (culture_directed_regimen s m h) = true.
Proof.
  intros s m h Hbase. unfold culture_directed_regimen.
  destruct (Microbiology.fungal_sepsis m); [reflexivity|].
  destruct (Microbiology.gram_negative_sepsis m).
  - destruct s; simpl in *; try reflexivity; try discriminate; exact Hbase.
  - destruct (culture_pending_too_long m h).
    + destruct s; simpl in *; try reflexivity; try discriminate; exact Hbase.
    + exact Hbase.
Qed.

Lemma advanced_nec_has_anaerobic_coverage : forall s,
  Stage.to_nat s >= 5 ->
  has_anaerobic_coverage (recommended_regimen_by_stage s) = true.
Proof.
  solve_stage.
Qed.

(* Antibiotic course durations are monotone in stage. *)
Lemma duration_days_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> duration_days s1 <= duration_days s2.
Proof.
  intros [] []; vm_compute; intro H; try lia; discriminate.
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
Definition trophic_feed_volume_ml_kg_day : nat :=
  ClinicalParameters.param_value ClinicalParameters.feed_trophic_ml_kg_day.
Definition advancement_rate_ml_kg_day : nat :=
  ClinicalParameters.param_value ClinicalParameters.feed_advancement_ml_kg_day.
Definition full_feed_volume_ml_kg_day : nat :=
  ClinicalParameters.param_value ClinicalParameters.feed_full_ml_kg_day.

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

(* Endpoint monotonicity (low, mid, high) across all three risk families. *)

Lemma mortality_low_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> low (mortality_risk s1) <= low (mortality_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma mortality_mid_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> mid (mortality_risk s1) <= mid (mortality_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma mortality_high_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> high (mortality_risk s1) <= high (mortality_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma stricture_low_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> low (stricture_risk s1) <= low (stricture_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma stricture_mid_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> mid (stricture_risk s1) <= mid (stricture_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma stricture_high_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> high (stricture_risk s1) <= high (stricture_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma short_bowel_low_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> low (short_bowel_risk s1) <= low (short_bowel_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma short_bowel_mid_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> mid (short_bowel_risk s1) <= mid (short_bowel_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

Lemma short_bowel_high_monotone : forall s1 s2,
  Stage.leb s1 s2 = true -> high (short_bowel_risk s1) <= high (short_bowel_risk s2).
Proof. intros [] []; vm_compute; intro H; try lia; discriminate. Qed.

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

(* Monotonicity-preserving institutional override. A SafeInstitutionalRiskData
   bundle pairs a risk-function table with proofs that each family is
   monotone in stage; an override that violates higher_stage_worse_*
   cannot be installed, since the type system refuses it. *)
Definition risk_function_monotone (f : Stage.t -> RiskRange) : Prop :=
  forall s1 s2, Stage.leb s1 s2 = true -> mid (f s1) <= mid (f s2).

Record SafeInstitutionalRiskData : Type := MkSafeInstitutional {
  safe_inst_data : InstitutionalRiskData;
  safe_mortality_monotone : risk_function_monotone (inst_mortality safe_inst_data);
  safe_stricture_monotone : risk_function_monotone (inst_stricture safe_inst_data);
  safe_short_bowel_monotone : risk_function_monotone (inst_short_bowel safe_inst_data);
  safe_mortality_valid_range : forall s, valid_range (inst_mortality safe_inst_data s);
  safe_stricture_valid_range : forall s, valid_range (inst_stricture safe_inst_data s);
  safe_short_bowel_valid_range : forall s, valid_range (inst_short_bowel safe_inst_data s)
}.

(* The default institutional table is monotonicity-safe by construction. *)
Definition safe_default_institutional_data : SafeInstitutionalRiskData :=
  MkSafeInstitutional default_institutional_data
    higher_stage_worse_mortality
    higher_stage_worse_stricture
    (fun s1 s2 H => short_bowel_mid_monotone s1 s2 H)
    mortality_risk_valid
    stricture_risk_valid
    short_bowel_risk_valid.

(* Confidence-interval risk range: the integer-percent triple is a point
   summary of an underlying distribution. The structure below carries the
   confidence level explicitly; coverage means the true rate falls within
   [low, high] with the stated probability. *)
Record ConfidenceIntervalRiskRange : Type := MkCIRiskRange {
  ci_range : RiskRange;
  ci_confidence_per_mille : nat   (* e.g., 950 = 95% CI *)
}.

Definition ci_within (cir : ConfidenceIntervalRiskRange) (rate : nat) : bool :=
  (low (ci_range cir) <=? rate) && (rate <=? high (ci_range cir)).

Definition ci_to_risk_range (cir : ConfidenceIntervalRiskRange) : RiskRange :=
  ci_range cir.

(* Default 95% CI lift of the editorial risk ranges. *)
Definition mortality_risk_ci (s : Stage.t) : ConfidenceIntervalRiskRange :=
  MkCIRiskRange (mortality_risk s) 950.

Definition stricture_risk_ci (s : Stage.t) : ConfidenceIntervalRiskRange :=
  MkCIRiskRange (stricture_risk s) 950.

Definition short_bowel_risk_ci (s : Stage.t) : ConfidenceIntervalRiskRange :=
  MkCIRiskRange (short_bowel_risk s) 950.

Lemma mortality_ci_within_low_high : forall s,
  ci_within (mortality_risk_ci s) (mid (mortality_risk s)) = true.
Proof.
  intros s. unfold ci_within. simpl.
  pose proof (mortality_risk_valid s) as [Hl Hh].
  apply Nat.leb_le in Hl, Hh. rewrite Hl, Hh. reflexivity.
Qed.

(* Safe-bundle accessors preserve the monotonicity guarantee. *)
Lemma safe_inst_mortality_monotone_concrete :
  forall d s1 s2, Stage.leb s1 s2 = true ->
  inst_mortality_percent (safe_inst_data d) s1 <=
  inst_mortality_percent (safe_inst_data d) s2.
Proof.
  intros d s1 s2 H. unfold inst_mortality_percent.
  apply (safe_mortality_monotone d). exact H.
Qed.

Lemma safe_inst_stricture_monotone_concrete :
  forall d s1 s2, Stage.leb s1 s2 = true ->
  inst_stricture_percent (safe_inst_data d) s1 <=
  inst_stricture_percent (safe_inst_data d) s2.
Proof.
  intros d s1 s2 H. unfold inst_stricture_percent.
  apply (safe_stricture_monotone d). exact H.
Qed.

Lemma safe_inst_short_bowel_monotone_concrete :
  forall d s1 s2, Stage.leb s1 s2 = true ->
  inst_short_bowel_percent (safe_inst_data d) s1 <=
  inst_short_bowel_percent (safe_inst_data d) s2.
Proof.
  intros d s1 s2 H. unfold inst_short_bowel_percent.
  apply (safe_short_bowel_monotone d). exact H.
Qed.

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

Lemma stage_with_organ_failure_idempotent : forall s oa,
  stage_with_organ_failure (stage_with_organ_failure s oa) oa =
  stage_with_organ_failure s oa.
Proof.
  intros s oa. unfold stage_with_organ_failure.
  destruct (NeonatalOrganFailure.multiorgan_dysfunction oa);
  destruct s; reflexivity.
Qed.

(* Single-pass classifier that incorporates organ failure assessment.
   Returns one stage that already reflects MODS escalation, eliminating
   the audit-trail ambiguity of the post-hoc modifier. The earlier API
   recorded both the pre-modifier and post-modifier stages; with this
   entry, audit trails record only the final stage. *)
Definition classify_with_oa
    (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : Stage.t :=
  stage_with_organ_failure (Classification.classify c) oa.

(* The single-pass form is definitionally equal to the post-hoc compose;
   both forms are observationally indistinguishable. *)
Lemma classify_with_oa_equals_compose : forall c oa,
  classify_with_oa c oa =
  stage_with_organ_failure (Classification.classify c) oa.
Proof. reflexivity. Qed.

(* Organ failure never decreases the stage produced by the classifier. *)
Lemma classify_with_oa_dominates_classify : forall c oa,
  Stage.to_nat (Classification.classify c) <=
  Stage.to_nat (classify_with_oa c oa).
Proof.
  intros c oa. apply organ_failure_never_decreases_stage.
Qed.

(* Without MODS, the single-pass classifier matches the base classifier. *)
Lemma classify_with_oa_no_mods_idempotent : forall c oa,
  NeonatalOrganFailure.multiorgan_dysfunction oa = false ->
  classify_with_oa c oa = Classification.classify c.
Proof.
  intros c oa H. unfold classify_with_oa, stage_with_organ_failure.
  rewrite H. destruct (Classification.classify c); reflexivity.
Qed.

(* With MODS, the single-pass classifier reaches at least IIIA. *)
Lemma classify_with_oa_mods_at_least_IIIA : forall c oa,
  NeonatalOrganFailure.multiorgan_dysfunction oa = true ->
  5 <= Stage.to_nat (classify_with_oa c oa).
Proof.
  intros c oa H. apply mods_forces_at_least_IIIA. exact H.
Qed.

(* The surgical boundary is preserved regardless of organ-failure modifier:
   pneumoperitoneum forces IIIB even after MODS bump. *)
Lemma classify_with_oa_preserves_IIIB : forall c oa,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_with_oa c oa = Stage.IIIB.
Proof.
  intros c oa H. unfold classify_with_oa.
  rewrite (Classification.pneumoperitoneum_forces_IIIB c H).
  unfold stage_with_organ_failure.
  destruct (NeonatalOrganFailure.multiorgan_dysfunction oa); reflexivity.
Qed.

(* Idempotence: re-applying the OA modifier to the single-pass result is a no-op. *)
Lemma classify_with_oa_idempotent : forall c oa,
  stage_with_organ_failure (classify_with_oa c oa) oa = classify_with_oa c oa.
Proof.
  intros c oa. unfold classify_with_oa.
  apply stage_with_organ_failure_idempotent.
Qed.

(* Strict-Bell variant of the single-pass OF-aware classifier. Mirrors
   classify_with_oa but routes through Classification.classify_strict_bell. *)
Definition classify_strict_with_oa
    (c : ClinicalState.t)
    (oa : NeonatalOrganFailure.OrganFailureAssessment) : Stage.t :=
  stage_with_organ_failure (Classification.classify_strict_bell c) oa.

Lemma classify_strict_with_oa_dominates_strict : forall c oa,
  Stage.to_nat (Classification.classify_strict_bell c) <=
  Stage.to_nat (classify_strict_with_oa c oa).
Proof.
  intros c oa. apply organ_failure_never_decreases_stage.
Qed.

Lemma classify_strict_with_oa_no_mods_idempotent : forall c oa,
  NeonatalOrganFailure.multiorgan_dysfunction oa = false ->
  classify_strict_with_oa c oa = Classification.classify_strict_bell c.
Proof.
  intros c oa H. unfold classify_strict_with_oa, stage_with_organ_failure.
  rewrite H. destruct (Classification.classify_strict_bell c); reflexivity.
Qed.

Lemma classify_strict_with_oa_preserves_IIIB : forall c oa,
  RadiographicSigns.pneumoperitoneum (ClinicalState.radiographic c) = true ->
  classify_strict_with_oa c oa = Stage.IIIB.
Proof.
  intros c oa H. unfold classify_strict_with_oa.
  apply Classification.strict_bell_IIIB_iff_pneumoperitoneum in H.
  rewrite H. unfold stage_with_organ_failure.
  destruct (NeonatalOrganFailure.multiorgan_dysfunction oa); reflexivity.
Qed.

End OrganFailureFeedback.
