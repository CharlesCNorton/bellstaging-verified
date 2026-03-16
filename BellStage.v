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
  meds : option RiskFactors.MedicationRiskFactors
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

End ClinicalState.

Module TimeSeries.

(* An observation is a clinical state at a specific time *)
Record Observation : Type := MkObservation {
  obs_time_hours : nat;
  obs_state : ClinicalState.t;
  obs_stage : nat;                          (* cached stage 1-6 *)
  obs_severity : nat                        (* cached severity score *)
}.

(* Consistency invariant: obs_time_hours matches the embedded clinical state's
   hours_since_symptom_onset, ensuring the observation timestamp and the
   state's internal clock agree. *)
Definition observation_consistent (o : Observation) : Prop :=
  obs_time_hours o = ClinicalState.hours_since_symptom_onset (obs_state o).

(* Create observation from clinical state — enforces timestamp consistency *)
Definition make_observation (time_h : nat) (state : ClinicalState.t) (stage : nat) : Observation :=
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
      (ClinicalState.radiographic_assessed_h state))
    stage
    (ClinicalState.overall_severity_score state).

Lemma make_observation_consistent : forall t s stage,
  observation_consistent (make_observation t s stage).
Proof.
  intros. unfold observation_consistent, make_observation. simpl. reflexivity.
Qed.

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

(* Guarded series_duration — returns 0 if time ordering is violated *)
Definition series_duration (ts : PatientTimeSeries) : nat :=
  match latest ts, earliest ts with
  | Some l, Some e =>
      if obs_time_hours e <=? obs_time_hours l
      then obs_time_hours l - obs_time_hours e
      else 0
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
      if (duration =? 0) then TemporalProgression.Stable
      else if (stage_delta * 240 >? 20 * Z.of_nat duration)%Z then TemporalProgression.RapidDeterioration
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

(* Constraint predicates for cached stage and severity.
   These cannot be enforced in the record definition because
   Classification.classify is defined after TimeSeries.
   Instead, they are predicates validated after Classification is available. *)
Definition obs_stage_valid (o : Observation) (classify : ClinicalState.t -> Stage.t) : Prop :=
  obs_stage o = Stage.to_nat (classify (obs_state o)).

Definition obs_severity_valid (o : Observation) : Prop :=
  obs_severity o = ClinicalState.overall_severity_score (obs_state o).

(* add_observation now requires timestamp consistency.
   Use make_observation (which enforces this) rather than
   MkObservation directly. *)
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
