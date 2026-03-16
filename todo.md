1. Use Section and Context declarations to reduce universally quantified variable boilerplate.
2. Adopt a consistent naming convention across all modules: either t-style (Coq stdlib) or descriptive names, not both.
3. Stop opening modules to avoid naming collisions; use qualified names instead of renaming definitions (no_signs, systemic_severity, etc.).
4. Add a CurrentClinicalState wrapper type or phantom-type mechanism to prevent callers from using classify on stale data instead of classify_checked.
5. Resolve the effective_hypotension divergence between structured VitalSigns and boolean SystemicSigns.hypotension so the same patient cannot stage differently depending on data representation.
6. Add input validation to ClinicalState.t construction so that clinically impossible combinations (GA=0, BW=0, pH=0) are rejected or flagged.
7. Enforce obs_stage and obs_severity cached values in TimeSeries.Observation via a smart constructor or dependent type rather than leaving obs_stage_valid and obs_severity_valid as unforced predicates.
8. Add a guard in compute_trajectory to check time ordering before computing obs_time_hours l - obs_time_hours e.
9. Add a witness or test demonstrating handling of the None case returned by add_observation when time ordering or consistency checks fail.
10. Clarify the semantics of first_at_stage with a comment or rename specifying that it returns the chronologically earliest observation meeting the threshold.
11. Construct a well_founded proof or Acc-based termination argument for the management phase DAG, not just a chain-of-length-2 bound.
12. Strengthen all_paths_terminate from reachability (exists a path to terminal) to operational termination (every execution of a transition function reaches terminal in bounded steps).
13. Prove that classify_stage default fall-through to Stage.IA is conservative: state explicitly that the mildest stage is the safe default when no pattern matches, or add an anomaly flag for unmatched input combinations.
14. Add a formal safety specification defining what it means for the classifier to be safe (e.g., never understaging a patient with confirmed advanced NEC) and prove it.
15. Prove that adding a specific clinical finding to a ClinicalState produces a ci_subset-related pair, bridging the abstract monotonicity theorem to concrete clinical scenarios.
16. Add a completeness proof for diagnose: every ConfirmedNEC diagnosis has findings that constitute confirmed NEC per the staging criteria.
17. Constrain classify_surjective witnesses to clinically plausible inputs (e.g., IIIB witness should have nonzero systemic and intestinal signs alongside pneumoperitoneum).
18. Add a systematic analysis of which ClinicalState fields are actually read by classify_stage, and prove that all unread fields are irrelevant (generalizing classify_independent_of_timestamp to all unused fields).
19. Characterize the clinical impact of the 3-ordinal-stage maximum divergence between classify_stage and classify_declarative in terms of treatment differences (NPO duration, antibiotic regimen, prognosis communication).
20. Model partial information explicitly: treat None labs/coag/vitals as prompting test ordering rather than defaulting to normal.
21. Wire WeightForGA classification (classify_weight_for_ga, is_sga) into risk scoring or staging so SGA status affects clinical decisions.
22. Wire postmenstrual_age and in_peak_nec_window into risk scoring or differential diagnosis so age-adjusted NEC likelihood is used.
23. Wire rapid_feed_advancement_threshold into risk scoring so rapid feeding advancement contributes to NEC risk.
24. Wire age_adjusted_nec_likelihood, age_adjusted_volvulus_likelihood, and age_adjusted_sip_likelihood into most_likely_diagnosis so differential diagnosis uses age context.
25. Wire UltrasoundFindings into the classifier or into a multi-modal imaging integration layer so ultrasound data affects staging.
26. Wire ImagingModality into RadiographicSigns so the classifier can distinguish X-ray from ultrasound from CT findings and apply modality-appropriate sensitivity weighting.
27. Wire MixedPresentation.diagnose_mixed into the diagnostic pipeline and add tests and theorems covering its behavior.
28. Build a bridge function that derives SurgicalContext from ClinicalState so the two parallel models are connected.
29. Add SIP-specific staging and treatment protocol so patients diagnosed as SuspectedSIP are not routed through NEC-specific surgical treatment.
30. Model NEC totalis and extent of disease so the staging system distinguishes focal necrosis from pan-intestinal necrosis.
31. Expand initial_procedure_for_perforation to consider bowel viability, extent of necrosis, and anatomic location in addition to birth weight and hemodynamic stability.
32. Expand requires_stoma beyond a single 50% threshold to consider bowel viability, location, and patient stability.
33. Add an antibiotic de-escalation pathway for culture-negative results so culture_directed_regimen supports stewardship, not just escalation.
34. Model antibiotic adverse effects (gentamicin nephrotoxicity, vancomycin nephrotoxicity, meropenem seizure risk) in the antibiotic selection logic.
35. Add gestational-age-adjusted lab thresholds so WBC, ANC, platelet, and other normal ranges vary by GA and postnatal day.
36. Model serial biomarker trending (CRP trend, platelet trend, lactate trend) as diagnostic and staging inputs instead of single point-in-time snapshots.
37. Model vital sign trending and heart rate variability as NEC risk predictors.
38. Model enteral feeding type and rate as classification inputs so current feeding status affects staging decisions.
39. Model NPO compliance so accidental feeding during NPO or partial compliance is representable.
40. Assign NEC recurrence a risk probability and model it in the temporal and diagnostic pathways.
41. Model short bowel syndrome progression (parenteral nutrition dependence, intestinal adaptation, transplant criteria) as a post-NEC outcome pathway.
42. Add confidence intervals, sample sizes, and heterogeneity assessments to Prognosis risk ranges instead of editorial low/mid/high estimates.
43. Calibrate DifferentialDiagnosis confidence weights against institutional case series or derive them via logistic regression rather than editorial assignment.
44. Add a formal model of NEC prevention interventions (probiotics, standardized feeding protocols, breast milk promotion).
45. Add a probabilistic or confidence-interval model so predicates can express diagnostic uncertainty rather than returning only bool.
46. Model organ failure attribution so stage_with_organ_failure distinguishes MODS caused by NEC from MODS caused by unrelated conditions.
47. Model organ_systems_failing to account for total dysfunction severity, not just count of organs above threshold, so diffuse mild dysfunction and catastrophic single-organ failure are distinguishable.
48. Model the clinical workflow connecting hours_to_reassess to actual clinical actions (when to order labs, when to image, when to reassess).
49. Model resource constraints (NICU bed availability, surgical team availability, blood product availability) as factors in clinical decision pathways.
50. Model informed consent and family preferences (comfort care, surgical refusal) as decision pathway branches.
51. Add a versioning scheme for the clinical model so staging decisions can be traced to a specific version of the clinical knowledge base.
52. Add an audit trail model (who ran the classifier, when, with what inputs, what result) for clinical decision support accountability.
53. Add JSON, protobuf, or FHIR serialization for all clinical types so the formalization can integrate with healthcare data interchange standards.
54. Add a specification for EHR integration (REST API or service interface) describing how the classifier would be invoked from a clinical system.
55. Add localization support so drug names, thresholds, and clinical parameters can vary by country or institution.
56. Add a multi-patient population model supporting cohort analysis, population-level statistics, and epidemiological modeling.
57. Add a formal specification of the relationship between nec_confidence/sip_confidence scores and diagnostic accuracy (calibration curve or probabilistic semantics).
58. Add a formal refinement proof that the extracted OCaml program behaves identically to the Coq specification under all inputs.
59. Add a formal equivalence statement between classify_stage and a specific published table (e.g., Walsh-Kliegman 1986 Table 1) making the correctness claim explicit rather than implicit.
