From Stdlib Require Import Extraction.

From BellStaging Require Import BellParams.
From BellStaging Require Import BellSigns.
From BellStaging Require Import BellStage.
From BellStaging Require Import BellClassification.

Module ExtractionDirectives.

(* Extraction directives targeting OCaml.
   These extract the core classifier and treatment logic to executable code. *)

Extraction Language OCaml.

Recursive Extraction
  Classification.classify
  Classification.classify_checked
  Classification.diagnose
  Classification.urgency_from_trajectory
  TrajectoryClassification.recommended_reassess_hours
  TrajectoryClassification.classify_with_trajectory
  TrajectoryClassification.escalation_warranted
  Treatment.of_stage
  Treatment.requires_surgery
  SurgicalIndications.surgery_indicated
  SurgicalProcedures.initial_procedure_for_perforation
  Antibiotics.culture_directed_regimen
  FeedingProtocol.can_restart_feeds
  RiskFactors.risk_score
  RiskFactors.high_risk
  DifferentialDiagnosis.most_likely_diagnosis
  Prognosis.mortality_risk
  Prognosis.stricture_risk
  Prognosis.short_bowel_risk.

End ExtractionDirectives.
