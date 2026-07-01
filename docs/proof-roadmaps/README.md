# Proof Roadmaps and Calculation Ledgers

This folder contains the linear proof roadmap for the Erdős #81 chordal branch preprint series.

The purpose is to make the final proof readable without requiring the reader to inspect the historical gate notes.

The gates remain valuable research records, but the formal proof chain is:

\[
\text{Paper A} \rightarrow \text{Paper B} \rightarrow \text{Paper C} \rightarrow \text{Paper D}.
\]

Each paper may cite earlier papers only. Later papers may not be used as inputs to earlier papers.

## Files

- `00_dependency_discipline.md`  
  Formal dependency rules and citation discipline.

- `01_global_proof_map.md`  
  One-page global proof map for the full chordal-branch program.

- `paper_B_proof_roadmap.md`  
  Roadmap for the local chordal toolkit.

- `paper_B_calculation_ledger.md`  
  Step-by-step calculations used by Paper B.

- `paper_C_proof_roadmap.md`  
  Roadmap for the fractional chordal assembly theorem.

- `paper_C_calculation_ledger.md`  
  Step-by-step calculations used by Paper C.

- paper_D_proof_roadmap.md  
  Roadmap for the integral chordal clique-partition theorem.

- paper_D_calculation_ledger.md  
  Step-by-step calculation ledger used by Paper D.

- `l4_certificate_usage.md`  
  Exact role of the \(L_4\) certificate and boundary-export logic.

- `reviewer_sensitive_points.md`  
  Short list of points most likely to be inspected by a reviewer.

- `v02_to_v03_reviewer_corrections.md`  
  Record of corrections incorporated into the public v0.3 manuscripts.

- `final_v03_public_status.md`  
  Current public-status note for the v0.3 repository organization.

## Guiding principle

The papers should not cite the gates as proof objects.  
Any gate-derived argument used in the final proof must be restated either in the paper itself, in a roadmap, or in a calculation ledger.

The \(L_4\) certificate is retained as a finite exact validation artifact for the final local residue. It is not used as an unrestricted window-sweep theorem.
