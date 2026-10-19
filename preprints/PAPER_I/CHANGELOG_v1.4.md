# Paper I v1.4 — editorial changelog

19 October 2026. Juan Pablo Traverso Gianini.

Baseline: [v1.3](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/01_manuscript), commit `eb335845bfa23375d5040ea31fc4f4b366346287`. This is an editorial edition; no mathematical result, hypothesis, exceptional case, constant, equation label or proof dependency is changed.

| Change | Scope | Mathematical effect |
|---|---|---|
| Compact title and publication metadata | EN/ES articles | None |
| Update the place of IV and V in the series | Introduction and discussion | Corrects historical framing; later papers are not new proof inputs |
| Separate formalization and reproducibility document | Recorded Lean interfaces, frozen sources, axioms and computational checks | Same evidence and formal scope; no new Lean/Lake build |
| Sentence punctuation outside boxed formulas | Display typography | Expressions and labels unchanged |
| Series typesetting and navigable links | MD/TeX/PDF/HTML | No mathematical change |

The numerical estimate is preserved; the affine-profile reduction remains the methodological focus. The finite-duality proof and all orbit boundary cases remain in the article.

The historical prior-art audit remains attached to its original snapshot. This edition makes no new historical-priority claim and is not new human peer review. Original AI disclosures are retained rather than attributing unverified tool use to an earlier paper.

The unchanged formal package is `lean_v1.2_freeze`. [Frozen sources and original verification](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/05_formalization). The source ZIP hash and every tracked frozen-file Git object are recorded in the new audit. Source and dependency licenses are unchanged, including later repository-level grants where applicable.

En español: cambios exclusivamente editoriales. Se conserva la matemática, se actualiza el contexto de la serie y se separa el complemento de formalización. No se recompila Lean/Lake ni se sustituyen las evidencias históricas por una supuesta auditoría nueva del kernel.

[Internal editorial audit](02_validation/01_INTERNAL_AUDITS/run_v1.4_editorial_release/10_REPORT/FINAL_INTERNAL_AUDIT_REPORT.md) · [Exact EN diff](02_validation/01_INTERNAL_AUDITS/run_v1.4_editorial_release/20_EVIDENCE/DIFF_en.patch) · [Exact ES diff](02_validation/01_INTERNAL_AUDITS/run_v1.4_editorial_release/20_EVIDENCE/DIFF_es.patch) · [Integrity manifest](04_integrity/EDITORIAL_v1.4/README.md).
