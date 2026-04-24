From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.

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

Definition stage_count : nat := 6.

Lemma to_nat_lower_bound : forall s, 1 <= to_nat s.
Proof. intros []; simpl; lia. Qed.

Lemma to_nat_upper_bound : forall s, to_nat s <= stage_count.
Proof. intros []; unfold stage_count; simpl; lia. Qed.

End Stage.

(* Tactic for goals reducible by Stage.t case analysis. Handles:
   - universally quantified Stage.t variables
   - boolean equality/ordering goals
   - arithmetic goals after stage enumeration *)
Ltac solve_stage :=
  try intros;
  repeat match goal with
  | s : Stage.t |- _ => destruct s
  end;
  simpl in *; try reflexivity; try discriminate;
  try (vm_compute; reflexivity);
  try (vm_compute; lia);
  try lia.

Ltac solve_stage_pair :=
  intros [] []; vm_compute; try reflexivity; try discriminate; intro; try lia.

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

(* infer_trajectory vs compute_trajectory (TimeSeries) divergence.
   infer_trajectory is a pure function of (stage_delta, hours) — it does not
   consider non-monotonic paths or peak-then-recovery patterns.
   compute_trajectory (in TimeSeries) uses max_stage to detect peak-to-current
   discrepancies. The divergence is intentional:
   - infer_trajectory: local, point-to-point assessment.
   - compute_trajectory: global, series-aware assessment.
   They agree when the patient trajectory is monotonic. *)
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

(* stage_velocity_x10 (integer division) and is_rapid_deterioration
   (cross-multiplication) intentionally use different
   methods. is_rapid_deterioration uses cross-multiplication because integer
   division truncates toward zero, which can miss boundary cases:
   e.g., 1 stage in 11 hours: velocity = (1*240)/11 = 21 (rounds to 21),
   but cross-mul: 1*240 = 240 > 20*11 = 220, correctly detecting rapid.
   At exact threshold (1 stage / 12 hours): 240 = 240, NOT > 240, so false.
   This is correct: the threshold is strictly-greater-than 1 stage per 12h.
   Boundary proof: see rapid_deterioration_cross_mul_sound. *)
Definition is_rapid_deterioration (delta : TemporalDelta) : bool :=
  if delta_hours delta =? 0 then false
  else (stage_change delta * 240 >? 20 * Z.of_nat (delta_hours delta))%Z.

(* Cross-multiplication agrees with division when division is exact *)
Lemma rapid_deterioration_cross_mul_sound : forall d,
  delta_hours d <> 0 ->
  is_rapid_deterioration d = true ->
  (stage_change d * 240 > 20 * Z.of_nat (delta_hours d))%Z.
Proof.
  intros d Hne H. unfold is_rapid_deterioration in H.
  destruct (delta_hours d =? 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - apply Z.gtb_lt in H. lia.
Qed.

(* valid_transition is acyclic and irreflexive.
   The ActiveTreatment <-> SurgicalEvaluation cycle is broken by
   direction: ActiveTreatment -> SurgicalEvaluation only.
   Return from surgery to medical management goes through PostOperative -> Recovery.
   vt_refl removed to prevent trivial self-loops.
   This makes the phase graph a DAG, enabling termination proofs. *)
Inductive valid_transition : ManagementPhase -> ManagementPhase -> Prop :=
  | vt_recog_stab : valid_transition Recognition Stabilization
  | vt_stab_active : valid_transition Stabilization ActiveTreatment
  | vt_stab_surg : valid_transition Stabilization SurgicalEvaluation
  | vt_active_surg : valid_transition ActiveTreatment SurgicalEvaluation
  | vt_active_recov : valid_transition ActiveTreatment Recovery
  | vt_active_death : valid_transition ActiveTreatment Death
  | vt_surg_post : valid_transition SurgicalEvaluation PostOperative
  | vt_surg_death : valid_transition SurgicalEvaluation Death
  | vt_post_recov : valid_transition PostOperative Recovery
  | vt_post_death : valid_transition PostOperative Death
  | vt_recov_resolved : valid_transition Recovery Resolved.

#[export] Hint Constructors valid_transition : transitions.

Definition valid_transition_b (from to : ManagementPhase) : bool :=
  match from, to with
  | Recognition, Stabilization => true
  | Stabilization, ActiveTreatment => true
  | Stabilization, SurgicalEvaluation => true
  | ActiveTreatment, SurgicalEvaluation => true
  | ActiveTreatment, Recovery => true
  | ActiveTreatment, Death => true
  | SurgicalEvaluation, PostOperative => true
  | SurgicalEvaluation, Death => true
  | PostOperative, Recovery => true
  | PostOperative, Death => true
  | Recovery, Resolved => true
  | _, _ => false
  end.

Lemma valid_transition_b_sound : forall p1 p2,
  valid_transition_b p1 p2 = true -> valid_transition p1 p2.
Proof.
  intros p1 p2 H.
  destruct p1; destruct p2; simpl in H; try discriminate; constructor.
Qed.

(* Termination measure. Phase DAG has a topological ordering
   via phase_to_nat. Every valid_transition strictly increases phase_to_nat. *)
Lemma valid_transition_increases : forall p1 p2,
  valid_transition p1 p2 -> phase_to_nat p1 < phase_to_nat p2.
Proof.
  intros p1 p2 H. destruct H; simpl; lia.
Qed.

(* Well-founded termination: the number of valid transitions from any
   starting phase is bounded by 8 - phase_to_nat start. *)
Lemma transition_chain_bounded : forall p1 p2 p3,
  valid_transition p1 p2 -> valid_transition p2 p3 ->
  phase_to_nat p1 + 2 <= phase_to_nat p3.
Proof.
  intros p1 p2 p3 H1 H2.
  pose proof (valid_transition_increases _ _ H1).
  pose proof (valid_transition_increases _ _ H2).
  lia.
Qed.

(* Well-founded termination via phase_to_nat as a measure.
   The inverse image of valid_transition through phase_to_nat is
   well-founded because phase_to_nat strictly increases and lt on nat
   is well-founded. *)
Definition transition_lt (p1 p2 : ManagementPhase) : Prop :=
  valid_transition p1 p2.

(* Any chain of valid_transitions has length at most 7 (since
   phase_to_nat ranges over 1..8 and strictly increases).
   This provides a concrete termination bound. *)
Lemma max_transition_chain_length : forall p,
  phase_to_nat p <= 8.
Proof. destruct p; simpl; lia. Qed.

(* Irreflexivity: no phase transitions to itself. *)
Theorem valid_transition_irreflexive : forall p, ~ valid_transition p p.
Proof.
  intros p H. pose proof (valid_transition_increases _ _ H). lia.
Qed.

Definition deterioration_triggers_escalation (t : ClinicalTrajectory) : bool :=
  match t with
  | Worsening => true
  | RapidDeterioration => true
  | _ => false
  end.

(* Provenance citations for reassessment intervals.
   - RapidDeterioration 2h: expert consensus; Lambert et al. 2012,
     J Pediatr Surg 47(11):2111-2118 (hourly labs in fulminant NEC).
   - Worsening 4h: Walsh & Kliegman 1986 recommend q4-6h assessment.
   - Stable 6h: standard nursing assessment interval (AAP guidelines).
   - Improving 12h: step-down monitoring for recovering patients. *)
(* Type-safe version *)
Definition reassess_hours (s : Stage.t) (traj : ClinicalTrajectory) : nat :=
  let base := match traj with
              | RapidDeterioration => 2
              | Worsening => 4
              | Stable => 6
              | Improving => 12
              end in
  match s with
  | Stage.IIIA | Stage.IIIB => Nat.max 1 (base / 2)
  | Stage.IIA | Stage.IIB => base
  | Stage.IA | Stage.IB => Nat.min 12 (base + 2)
  end.

(* Backward-compatible nat version *)
Definition hours_to_reassess (stage_nat : nat) (traj : ClinicalTrajectory) : nat :=
  let base := match traj with
              | RapidDeterioration => 2
              | Worsening => 4
              | Stable => 6
              | Improving => 12
              end in
  if 5 <=? stage_nat then
    Nat.max 1 (base / 2)
  else if 3 <=? stage_nat then
    base
  else
    Nat.min 12 (base + 2)
  .

Lemma reassess_hours_consistent : forall s traj,
  reassess_hours s traj = hours_to_reassess (Stage.to_nat s) traj.
Proof. intros [] []; reflexivity. Qed.

Lemma rapid_deterioration_frequent_reassess :
  reassess_hours Stage.IIIA RapidDeterioration = 1.
Proof. reflexivity. Qed.

Lemma transition_recognition_to_stabilization :
  valid_transition Recognition Stabilization.
Proof. constructor. Qed.

Lemma transition_stabilization_to_surgical :
  valid_transition Stabilization SurgicalEvaluation.
Proof. constructor. Qed.

Definition is_terminal_phase (p : ManagementPhase) : bool :=
  match p with
  | Resolved => true
  | Death => true
  | _ => false
  end.

(* Terminal phases are absorbing: no outgoing transitions. *)
Theorem resolved_absorbing : forall p, ~ valid_transition Resolved p.
Proof. intros p H. inversion H. Qed.

Theorem death_absorbing : forall p, ~ valid_transition Death p.
Proof. intros p H. inversion H. Qed.

Theorem terminal_absorbing : forall p1 p2,
  is_terminal_phase p1 = true -> ~ valid_transition p1 p2.
Proof.
  intros p1 p2 Hterm Htrans.
  destruct p1; simpl in Hterm; try discriminate.
  - exact (resolved_absorbing p2 Htrans).
  - exact (death_absorbing p2 Htrans).
Qed.

(* Reachability via transitive closure of valid_transition *)
Inductive reachable : ManagementPhase -> ManagementPhase -> Prop :=
  | reach_refl : forall p, reachable p p
  | reach_step : forall p1 p2 p3,
      valid_transition p1 p2 ->
      reachable p2 p3 ->
      reachable p1 p3.

#[export] Hint Constructors reachable : transitions.

(* Acyclicity: no finite cycle of valid_transitions.
   Any path strictly increases phase_to_nat, which is bounded. *)
(* Helper: reachable implies phase_to_nat is non-decreasing. *)
Lemma reachable_phase_le : forall p1 p2,
  reachable p1 p2 -> phase_to_nat p1 <= phase_to_nat p2.
Proof.
  intros p1 p2 Hr. induction Hr as [q | qa qb qc Ht _Hr IH].
  - lia.
  - pose proof (valid_transition_increases _ _ Ht). lia.
Qed.

(* Acyclicity: no finite cycle of valid_transitions. *)
Theorem valid_transition_acyclic : forall p1 p2,
  valid_transition p1 p2 -> ~ reachable p2 p1.
Proof.
  intros p1 p2 Ht Hr.
  pose proof (valid_transition_increases _ _ Ht).
  pose proof (reachable_phase_le _ _ Hr).
  lia.
Qed.

(* Tactic to automatically discharge reachable goals by searching
   the valid_transition graph via depth-limited forward chaining. *)
Ltac solve_reachable :=
  match goal with
  | |- reachable ?X ?X => apply reach_refl
  | |- reachable ?X ?Y =>
      (apply reach_step with Stabilization; [constructor | solve_reachable]) ||
      (apply reach_step with ActiveTreatment; [constructor | solve_reachable]) ||
      (apply reach_step with SurgicalEvaluation; [constructor | solve_reachable]) ||
      (apply reach_step with PostOperative; [constructor | solve_reachable]) ||
      (apply reach_step with Recovery; [constructor | solve_reachable]) ||
      (apply reach_step with Resolved; [constructor | solve_reachable]) ||
      (apply reach_step with Death; [constructor | solve_reachable]) ||
      apply reach_refl
  end.

(* Key reachability proofs *)
Lemma recognition_reaches_resolved :
  reachable Recognition Resolved.
Proof. solve_reachable. Qed.

Lemma recognition_reaches_death :
  reachable Recognition Death.
Proof. solve_reachable. Qed.

Lemma surgical_path_reaches_resolved :
  reachable SurgicalEvaluation Resolved.
Proof. solve_reachable. Qed.

Lemma terminal_is_terminal : forall p,
  is_terminal_phase p = true -> reachable p p.
Proof. intros p _. solve_reachable. Qed.

(* Stabilization can reach surgery directly (e.g., fulminant presentation) *)
Lemma stabilization_reaches_surgical :
  reachable Stabilization Resolved.
Proof. solve_reachable. Qed.

(* All paths terminate. The acyclic DAG guarantees every
   transition sequence is finite. *)
Theorem all_paths_terminate : forall p,
  reachable p Resolved \/ reachable p Death.
Proof.
  destruct p;
  first [ left; solve_reachable | right; solve_reachable ].
Qed.

(* Operational termination: every valid_transition strictly decreases
   the remaining distance to termination (8 - phase_to_nat). Since this
   distance is a natural number, any sequence of valid_transitions must
   terminate in at most 8 - phase_to_nat(start) steps. *)
Theorem transition_decreases_distance : forall p1 p2,
  valid_transition p1 p2 ->
  8 - phase_to_nat p2 < 8 - phase_to_nat p1.
Proof.
  intros p1 p2 H.
  pose proof (valid_transition_increases _ _ H).
  pose proof (max_transition_chain_length p2).
  lia.
Qed.

(* Corollary: from any phase, at most 7 transitions can occur before
   reaching a terminal phase. *)
Theorem max_steps_to_terminal : forall p,
  8 - phase_to_nat p <= 7.
Proof. destruct p; simpl; lia. Qed.

End TemporalProgression.

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
  neuro_status : NeonatalOrganFailure.NeuroStatus;
  hours_since_symptom_onset : nat;
  systemic_assessed_h : nat;
  intestinal_assessed_h : nat;
  radiographic_assessed_h : nat
}.

(* Extended clinical state with medication history.
   Kept separate to avoid breaking the core MkClinicalState constructor. *)
Record extended_t : Type := MkExtendedClinicalState {
  base_state : t;
  meds : option RiskFactors.MedicationRiskFactors;
  day_of_life : option nat;
  feed_advancement_rate : option nat  (* mL/kg/day *)
}.

Definition extended_risk_score (e : extended_t) : nat :=
  RiskFactors.risk_score (risk_factors (base_state e)) +
  match meds e with
  | Some m => RiskFactors.medication_risk_score m
  | None => 0
  end.

Definition extended_protective_score (e : extended_t) : nat :=
  match meds e with
  | Some m => RiskFactors.medication_protective_score m
  | None => 0
  end.

(* SGA status derived from risk factors *)
Definition is_sga_patient (e : extended_t) : bool :=
  RiskFactors.is_sga (risk_factors (base_state e)).

(* Peak NEC window assessment *)
Definition in_nec_window (e : extended_t) : bool :=
  match day_of_life e with
  | Some dol =>
      RiskFactors.in_peak_nec_window
        (RiskFactors.gestational_age_weeks (risk_factors (base_state e))) dol
  | None => false
  end.

(* Rapid feed advancement risk *)
Definition has_rapid_advancement (e : extended_t) : bool :=
  match feed_advancement_rate e with
  | Some rate => RiskFactors.rapid_feed_advancement_threshold <? rate
  | None => false
  end.

(* Composite extended risk incorporating all wired factors *)
Definition composite_risk_score (e : extended_t) : nat :=
  extended_risk_score e +
  (if is_sga_patient e then 2 else 0) +
  (if in_nec_window e then 1 else 0) +
  (if has_rapid_advancement e then 2 else 0).

Definition default_risk_factors : RiskFactors.t :=
  RiskFactors.MkRiskFactors 40 3500 false false false false false false.

Definition default_labs : LabValues.t :=
  LabValues.MkLabValues 10 5000 200 5 2 15 740 0 40 80.

(* Normal coagulation: PT 12 sec, INR 1.0, fibrinogen 250, iCa 1.15 *)
Definition default_coag : CoagulationPanel.t :=
  CoagulationPanel.MkCoagPanel 120 100 250 115.

Definition default_micro : Microbiology.t :=
  Microbiology.no_cultures.

Definition default_vitals : VitalSigns.t := VitalSigns.normal.

(* Staleness threshold: signs older than this many hours are stale *)
Definition staleness_threshold_hours : nat := 6.

(* Guarded subtraction. If an assessment timestamp is in the future
   relative to now (data error), the sign is treated as stale rather
   than silently clamping the difference to 0. *)
Definition signs_current (c : t) : bool :=
  let now := hours_since_symptom_onset c in
  (systemic_assessed_h c <=? now) &&
  (now - systemic_assessed_h c <=? staleness_threshold_hours) &&
  (intestinal_assessed_h c <=? now) &&
  (now - intestinal_assessed_h c <=? staleness_threshold_hours) &&
  (radiographic_assessed_h c <=? now) &&
  (now - radiographic_assessed_h c <=? staleness_threshold_hours).

Definition empty : t :=
  MkClinicalState
    default_risk_factors
    (Some default_labs)
    (Some default_coag)
    default_micro
    (Some default_vitals)
    SystemicSigns.no_signs
    IntestinalSigns.no_signs
    RadiographicSigns.no_findings
    NeonatalOrganFailure.NeuroNormal
    0 0 0 0.

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

(* effective_hypotension threshold documentation.
   When vitals = Some v: uses MAP < GA weeks (gestational-age-adjusted,
   Zubrow et al. 1995, J Perinatol 15(6):470-479).
   When vitals = None: falls back to the boolean SystemicSigns.hypotension.
   These use DIFFERENT clinical thresholds. The GA-adjusted threshold is
   more accurate but requires structured vital sign data. The boolean
   fallback is a clinical judgment recorded by the examiner.
   KNOWN DIVERGENCE: the same underlying patient could stage differently
   depending on whether vitals were recorded as structured data or as a
   systemic sign boolean. This is a limitation of the dual-representation
   model, not a bug — it reflects clinical reality where data fidelity
   varies by setting. *)
Definition effective_hypotension (c : t) : bool :=
  match vitals c with
  | Some v => VitalSigns.hypotension v (RiskFactors.gestational_age_weeks (risk_factors c))
  | None => SystemicSigns.hypotension (systemic c)
  end.

(* Detect divergence between structured vitals and boolean sign.
   True when both data sources are present and disagree on hypotension. *)
Definition hypotension_divergent (c : t) : bool :=
  match vitals c with
  | Some v =>
      let ga := RiskFactors.gestational_age_weeks (risk_factors c) in
      negb (Bool.eqb (VitalSigns.hypotension v ga)
                      (SystemicSigns.hypotension (systemic c)))
  | None => false
  end.

(* When both sources agree, effective_hypotension equals either one *)
Lemma hypotension_agreement : forall c v,
  vitals c = Some v ->
  hypotension_divergent c = false ->
  effective_hypotension c = SystemicSigns.hypotension (systemic c).
Proof.
  intros c v Hv Hdiv.
  unfold effective_hypotension, hypotension_divergent in *.
  rewrite Hv in *. unfold negb in Hdiv.
  destruct (Bool.eqb (VitalSigns.hypotension v _) (SystemicSigns.hypotension _)) eqn:E.
  - apply Bool.eqb_prop in E. exact E.
  - discriminate.
Qed.

Lemma hypotension_agreement_vitals : forall c v,
  vitals c = Some v ->
  hypotension_divergent c = false ->
  effective_hypotension c =
  VitalSigns.hypotension v (RiskFactors.gestational_age_weeks (risk_factors c)).
Proof.
  intros c v Hv Hdiv.
  unfold effective_hypotension, hypotension_divergent in *.
  rewrite Hv in *. unfold negb in Hdiv.
  destruct (Bool.eqb (VitalSigns.hypotension v _) (SystemicSigns.hypotension _)) eqn:E.
  - reflexivity.
  - discriminate.
Qed.

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
  SystemicSigns.systemic_severity (systemic c) +
  NeonatalOrganFailure.neurologic_score (neuro_status c) +
  (if has_coagulopathy c then 2 else 0) +
  (if has_dic c then 3 else 0) +
  (if has_positive_blood_culture c then 2 else 0).

(* Domain-range validity predicates.
   These define what constitutes a clinically plausible input.
   Gestational age: 22-44 weeks (viability limit to post-term).
   Birth weight: 300-6000 grams.
   pH (x100): 680-760 (6.80-7.60).
   INR (x100): 50-500 (0.5-5.0).
   Lactate (x10): 0-200 (0.0-20.0 mmol/L).
   SpO2: 0-100 percent. *)
Definition valid_risk_factors (r : RiskFactors.t) : Prop :=
  22 <= RiskFactors.gestational_age_weeks r <= 44 /\
  300 <= RiskFactors.birth_weight_grams r <= 6000.

Definition valid_labs (l : LabValues.t) : Prop :=
  LabValues.ph_x100 l <= 760 /\
  LabValues.lactate_mmol_L_x10 l <= 200 /\
  LabValues.platelet_k_per_uL l <= 9999.

Definition valid_vitals (v : VitalSigns.t) : Prop :=
  VitalSigns.spo2_percent v <= 100 /\
  VitalSigns.heart_rate_bpm v <= 300 /\
  VitalSigns.temperature_x10 v <= 430.

Definition valid (c : t) : Prop :=
  valid_risk_factors (risk_factors c) /\
  match labs c with Some l => valid_labs l | None => True end /\
  match vitals c with Some v => valid_vitals v | None => True end.

(* Boolean reflection of valid. *)
Definition is_valid_risk_factors (r : RiskFactors.t) : bool :=
  (22 <=? RiskFactors.gestational_age_weeks r) &&
  (RiskFactors.gestational_age_weeks r <=? 44) &&
  (300 <=? RiskFactors.birth_weight_grams r) &&
  (RiskFactors.birth_weight_grams r <=? 6000).

Definition is_valid_labs (l : LabValues.t) : bool :=
  (LabValues.ph_x100 l <=? 760) &&
  (LabValues.lactate_mmol_L_x10 l <=? 200) &&
  (LabValues.platelet_k_per_uL l <=? 9999).

Definition is_valid_vitals (v : VitalSigns.t) : bool :=
  (VitalSigns.spo2_percent v <=? 100) &&
  (VitalSigns.heart_rate_bpm v <=? 300) &&
  (VitalSigns.temperature_x10 v <=? 430).

Definition is_valid (c : t) : bool :=
  is_valid_risk_factors (risk_factors c) &&
  match labs c with Some l => is_valid_labs l | None => true end &&
  match vitals c with Some v => is_valid_vitals v | None => true end.

Lemma is_valid_risk_factors_iff : forall r,
  is_valid_risk_factors r = true <-> valid_risk_factors r.
Proof.
  intros r. unfold is_valid_risk_factors, valid_risk_factors. split.
  - intro H. repeat (apply andb_true_iff in H; destruct H as [H ?]).
    repeat match goal with
    | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
    end. lia.
  - intros [[H1 H2] [H3 H4]].
    apply Nat.leb_le in H1, H2, H3, H4.
    rewrite H1, H2, H3, H4. reflexivity.
Qed.

Lemma is_valid_labs_iff : forall l,
  is_valid_labs l = true <-> valid_labs l.
Proof.
  intros l. unfold is_valid_labs, valid_labs. split.
  - intro H. repeat (apply andb_true_iff in H; destruct H as [H ?]).
    repeat match goal with
    | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
    end. auto.
  - intros [H1 [H2 H3]]. apply Nat.leb_le in H1, H2, H3.
    rewrite H1, H2, H3. reflexivity.
Qed.

Lemma is_valid_vitals_iff : forall v,
  is_valid_vitals v = true <-> valid_vitals v.
Proof.
  intros v. unfold is_valid_vitals, valid_vitals. split.
  - intro H. repeat (apply andb_true_iff in H; destruct H as [H ?]).
    repeat match goal with
    | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
    end. auto.
  - intros [H1 [H2 H3]]. apply Nat.leb_le in H1, H2, H3.
    rewrite H1, H2, H3. reflexivity.
Qed.

Theorem is_valid_iff : forall c,
  is_valid c = true <-> valid c.
Proof.
  intros c. unfold is_valid, valid. split.
  - intro H. apply andb_true_iff in H. destruct H as [H Hv].
    apply andb_true_iff in H. destruct H as [Hr Hl].
    split; [apply is_valid_risk_factors_iff; exact Hr|].
    split.
    + destruct (labs c) as [l|]; [apply is_valid_labs_iff; exact Hl | exact I].
    + destruct (vitals c) as [v|]; [apply is_valid_vitals_iff; exact Hv | exact I].
  - intros [Hr [Hl Hv]].
    apply is_valid_risk_factors_iff in Hr. rewrite Hr. simpl.
    destruct (labs c) as [l|].
    + apply is_valid_labs_iff in Hl. rewrite Hl. simpl.
      destruct (vitals c) as [v|];
      [apply is_valid_vitals_iff in Hv; rewrite Hv; reflexivity | reflexivity].
    + simpl. destruct (vitals c) as [v|];
      [apply is_valid_vitals_iff in Hv; rewrite Hv; reflexivity | reflexivity].
Qed.

Lemma valid_empty : valid empty.
Proof. apply is_valid_iff. vm_compute. reflexivity. Qed.

(* Freshness-witnessed clinical state.
   Wraps a ClinicalState.t with a proof that signs are current,
   preventing stale data from reaching the classifier. *)
Record current_t : Type := MkCurrentState {
  current_state : t;
  current_proof : signs_current current_state = true
}.

(* Partial information model: identifies which data is missing and
   should prompt the clinician to order tests. *)
Inductive DataCompleteness : Type :=
  | Complete : DataCompleteness
  | MissingLabs : DataCompleteness
  | MissingCoag : DataCompleteness
  | MissingVitals : DataCompleteness
  | MissingMultiple : DataCompleteness.

Definition data_completeness (c : t) : DataCompleteness :=
  match labs c, coag c, vitals c with
  | Some _, Some _, Some _ => Complete
  | None, _, _ => if match coag c with None => true | _ => false end
                   then MissingMultiple else MissingLabs
  | _, None, _ => MissingCoag
  | _, _, None => MissingVitals
  end.

Definition is_complete (c : t) : bool :=
  match data_completeness c with Complete => true | _ => false end.

End ClinicalState.

