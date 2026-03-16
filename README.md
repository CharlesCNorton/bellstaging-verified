# bellstaging-verified

Verified formalization of the modified Bell staging criteria for necrotizing enterocolitis (NEC) in neonates, written in Rocq (Coq) 9.

## What this is

A machine-checked implementation of the Walsh-Kliegman modified Bell staging system (Stages IA through IIIB) for NEC, covering:

- **Risk assessment** — gestational age, birth weight, feeding type, comorbidities, with literature-sourced weights
- **Classification** — two independent classifiers (procedural and declarative) with proved agreement on the surgical boundary (IIIB)
- **Treatment** — NPO duration, antibiotic regimen selection, culture-directed escalation
- **Surgical decision** — absolute/relative indications, procedure selection per the NET trial
- **Feeding protocol** — NPO duration by stage, refeeding criteria, recovery timeline
- **Temporal progression** — clinical trajectory, management phase DAG with proved termination
- **Differential diagnosis** — NEC vs SIP vs volvulus vs sepsis vs feeding intolerance
- **Prognosis** — mortality, stricture, and short bowel syndrome risk ranges by stage

## Key theorems

| Theorem | File | Meaning |
|---------|------|---------|
| `classify_inputs_monotone` | BellWitnesses.v | Adding clinical signs never decreases stage |
| `classify_agree_on_surgery` | BellCriteriaDecl.v | Both classifiers agree on IIIB (surgical boundary) |
| `classifiers_not_equivalent` | BellCriteriaDecl.v | The two classifiers genuinely disagree at intermediate stages |
| `perforation_always_surgical` | BellWitnesses.v | Pneumoperitoneum always triggers surgery |
| `no_perforation_not_IIIB` | BellWitnesses.v | Without perforation, IIIB is unreachable |
| `all_paths_terminate` | BellStage.v | Every management phase reaches Resolved or Death |
| `valid_transition_acyclic` | BellStage.v | The management phase graph has no cycles |
| `breast_milk_reduces_risk` | BellWitnesses.v | Switching from formula to breast milk strictly reduces risk |

## Building

Requires Rocq 9.0 and coq-quickchick.

```
make
```

## File structure

| File | Contents |
|------|----------|
| `BellParams.v` | Clinical parameters, risk factors, lab values, coagulation, microbiology, vital signs |
| `BellSigns.v` | Organ failure scoring, differential diagnosis, systemic/intestinal/radiographic signs |
| `BellStage.v` | Stage enum, diagnosis, temporal progression, clinical state, time series |
| `BellClassification.v` | Classifier, treatment, surgical indications, antibiotics, feeding, prognosis |
| `BellCriteriaDecl.v` | Declarative Bell criteria and classifier agreement analysis |
| `BellWitnesses.v` | Witness examples, safety properties, published case validations, sensitivity analysis |
| `BellExtraction.v` | OCaml extraction directives |
| `BellStagingQC.v` | QuickChick property-based tests |

## License

MIT
