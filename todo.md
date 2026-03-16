1. Cure: Add a `_CoqProject` file and build configuration so the formalization can be compiled reproducibly.
2. Cure: Prove that `BellStaging.v` compiles cleanly under Coq 8.19 and record the successful build output.
3. Cure: Constrain `obs_stage` in `TimeSeries.Observation` with a proof obligation that it equals `Stage.to_nat (Classification.classify (obs_state o))`.
4. Cure: Constrain `obs_severity` in `TimeSeries.Observation` with a proof obligation that it equals `ClinicalState.overall_severity_score (obs_state o)`.
5. Cure: Require `observation_consistent` as a precondition in `add_observation`, not just in `make_observation`.
6. Cure: Hide `MkObservation` behind a smart constructor or dependent record so that `obs_stage` and `obs_severity` cannot be set to values inconsistent with the embedded `ClinicalState`; the raw constructor is exposed and witness examples (lines 2418–2431) bypass `make_observation` with manually-chosen stage values that are not computed from the clinical state.
7. Cure: Add a well-founded decreasing measure to `valid_transition` to eliminate the `ActiveTreatment <-> SurgicalEvaluation` cycle and prove actual termination, not just reachability.
8. Cure: Strengthen `all_paths_terminate` from a reachability result to a termination result by removing or bounding the `vt_refl` self-loop constructor and the `ActiveTreatment <-> SurgicalEvaluation` cycle; currently a worsening patient can bounce between phases indefinitely while satisfying the relation.
9. Cure: Guard all nat subtractions (`compute_delta.delta_hours`, `culture_pending_too_long`, `signs_current`, `series_duration`) against underflow by adding preconditions or switching to `Z`.
10. Cure: Reject invalid temporal ordering (e.g., `current_h < collected_h`) at the type or precondition level rather than silently clamping to 0 via nat subtraction; in a clinical context, a future-dated collection time masked as zero elapsed hours could suppress escalation logic in `culture_pending_too_long` and misreport staleness in `signs_current`.
11. Cure: Add temporal ordering constraints to `Microbiology` so `blood_culture_collected_h <= blood_culture_resulted_h` is enforced.
12. Cure: Prove that `compute_trajectory` (TimeSeries) and `infer_trajectory` (TemporalProgression) agree on shared inputs, or document the intentional divergence.
13. Cure: Reconcile `stage_velocity_x10` (integer division) with `is_rapid_deterioration` (cross-multiplication) so both use the same truncation-safe method.
14. Cure: Analyze and prove correct boundary behavior of `stage_velocity_x10` at the rapid deterioration threshold under integer division truncation.
15. Cure: Prove that `classify_stage` requires systemic signs for Stage IIA, or document and justify the deviation from Bell's original criteria which require systemic signs at all stages.
16. Cure: Prove that `classify_stage` requires systemic signs for Stage IIB, or document and justify the deviation from Bell's original criteria (witness 3 at line 3432 shows IIB fires without systemic signs).
17. Cure: Document and justify that `classify_stage` returns Stage IIB with `systemic = none` (witness 3, line 3432), or add systemic signs as a required conjunct in the IIB branch; Bell's original criteria require systemic involvement at all stages above IA, and the current procedural classifier can escalate staging purely on intestinal and radiographic findings without any systemic illness.
18. Cure: Prove that `classify_stage` requires NEC-specific radiographic findings for Stage IIIA, or document that nonspecific findings like intestinal dilation alone can trigger IIIA.
19. Cure: Prove that `effective_hypotension` produces consistent staging regardless of whether vitals are `Some` or `None` for the same underlying clinical state.
20. Cure: Reconcile the two different clinical thresholds used by `effective_hypotension`: when `vitals = Some v`, hypotension is `MAP < GA weeks` (gestational-age-adjusted, line 1576); when `vitals = None`, it falls back to the fixed boolean `SystemicSigns.hypotension` (line 1577); the same underlying patient could stage differently depending on whether vitals were recorded as a structured record or as a systemic sign boolean.
21. Cure: Prove that `classify_stage` and `classify_declarative` agree on the IIIA boundary (14-day antibiotics vs 10-day).
22. Cure: Prove that `classify_stage` and `classify_declarative` agree on the Stage I vs Stage II boundary (suspected vs confirmed NEC).
23. Cure: Prove monotonicity of `urgency_from_trajectory` in stage: for a fixed trajectory, higher stages produce equal or higher urgency.
24. Cure: Prove that `recommended_reassess_hours` is monotonically decreasing with urgency level.
25. Cure: Prove the converse of `refeeding_requires_npo_elapsed`: that NPO elapsed + normal abdominal exam + no bilious residuals is sufficient to restart feeds.
26. Cure: Prove that `culture_directed_regimen` preserves gram-negative coverage when the base regimen has it, not just anaerobic coverage.
27. Cure: Prove that `culture_directed_regimen` never narrows overall spectrum compared to the base regimen (covers all three: gram-negative, anaerobic, and gram-positive when base does).
28. Cure: Remove or connect the unreachable differential diagnoses (`HirschsprungDisease`, `MeconiumIleus`, `IntestinalAtresia`) — either add matching pathways in `most_likely_diagnosis` or delete them.
29. Cure: Document and prove the implicit priority ordering in `most_likely_diagnosis` (pneumatosis > volvulus > sepsis > confidence scoring > feeding intolerance).
30. Cure: Prove that `nec_confidence` and `sip_confidence` weights produce correct differential rankings for all input combinations, not just tested witnesses, or add QuickChick property-based testing.
31. Cure: Provide verifiable calibration or explicit editorial justification for the integer weights in `nec_confidence` (5, 4, 2, 3) and `sip_confidence` (3, 2, 1, 2); the cited sensitivity/specificity data (Epelman 2007, Pumberger 2002, Attridge 2006) do not directly yield these values, making them editorial choices that should be flagged as such or derived from a documented methodology.
32. Cure: Prove that `risk_score` Z-score clamping at 0 does not cause clinically distinct low-risk patients to be grouped identically, or expose the Z-score in `high_risk` instead of the clamped nat.
33. Cure: Add provenance citations for `hours_to_reassess` magic numbers (2/4/6/12 hours) matching the file's convention of citing sources for all clinical thresholds.
34. Cure: Add provenance citations for `trophic_feed_volume_ml_kg_day` (20), `advancement_rate_ml_kg_day` (20), and `full_feed_volume_ml_kg_day` (150).
35. Cure: Add provenance citations for `mortality_risk`, `stricture_risk`, and `short_bowel_risk` range endpoints (currently only midpoints are discussed in comments).
36. Cure: Model gestational-age-dependent vital sign thresholds for tachycardia, bradycardia, and tachypnea instead of using fixed cutoffs for all ages.
37. Cure: Model postnatal age (day of life or corrected gestational age) as a risk factor, since NEC incidence peaks at 30-31 weeks postmenstrual age.
38. Cure: Model weight-for-gestational-age (SGA/AGA/LGA) classification as a risk factor, since SGA is a known NEC risk factor.
39. Cure: Model pre-NEC feeding advancement rate as a risk factor (Berseth 2003), distinct from the post-NEC refeeding protocol.
40. Cure: Model medication risk factors (indomethacin, H2 blockers, antenatal steroids) that affect NEC incidence.
41. Cure: Distinguish imaging modality (X-ray vs ultrasound vs CT) in `RadiographicSigns` since they have different sensitivities for pneumatosis and portal venous gas.
42. Cure: Model abdominal ultrasound findings (bowel wall thickening, echogenicity, perfusion) which are increasingly used for NEC staging.
43. Cure: Add age-dependent likelihood to `DifferentialDiagnosis` since volvulus, Hirschsprung, and meconium ileus have different age distributions.
44. Cure: Model mixed SIP/NEC presentations in `diagnose` instead of the current binary classification that forces SIP only when no NEC evidence exists.
45. Cure: Replace the 4-level `NeuroStatus` enum with a more granular neonatal neurologic assessment (Sarnat staging or equivalent).
46. Cure: Feed `NeonatalOrganFailure` scores back into staging, since Stage III clinically requires systemic compromise.
47. Cure: Parameterize `mortality_risk`, `stricture_risk`, and `short_bowel_risk` so institutional or era-specific data can be substituted without modifying definitions.
48. Cure: Add sensitivity analysis showing how threshold perturbation (e.g., thrombocytopenia 150 vs 100) affects staging classification across representative patient populations.
49. Cure: Add QuickChick property-based testing to validate invariants (monotonicity, bounds, surgical safety) against randomly generated `ClinicalState` values.
50. Cure: Add `Extraction` directives targeting OCaml or Haskell so the classifier can be compiled to executable code for clinical use.
51. Cure: Resolve module-level name collisions (`none`, `t`, `severity_score`) by renaming or ensuring no upstream breakage if modules are opened.
