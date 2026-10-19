# Paper IV v1.24 — editorial changelog / cambios editoriales

19 October 2026. Compared with [published v1.23](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/01_manuscript), commit `ef31294ad67dfe3f44bc47cec4791c836f55e8aa`.

## What changed

- Results and proof mechanisms now lead the abstract and introduction. Code identifiers in prose are replaced by the mathematical operations they denote.
- Formal source maps, literal Lean declarations, axiom scope, historical builds and reproduction details move into a separate bilingual formal companion. The article keeps one formalization paragraph.
- The proof map explains both construction branches, the eventual bound, its all-orders consequence and retained-root stability. Mathematical appendices and result numbering remain.
- Appendix F.5 prints the numerical premise already cited there, from frozen E34/L11Params.lean. It is an explanation of an existing step, not an added hypothesis or result.
- Periods remain grammatical punctuation. Two terminal signs per language move outside boxed expressions so the punctuation is visibly distinct from the formula.
- Local-review labels and the obsolete draft-status sentence are removed. AI/tool attribution and author responsibility remain.
- Paper IV has direct article/companion links in both languages and all three formats. Papers I–III READMEs and the series landing page now describe contributions and relationships; their manuscripts are unchanged.

## What did not change

No hypotheses, theorem conclusions, constants, labels, proof dependencies, mathematical scope or priority claims changed. All 237 original displayed equations remain in order, modulo the stated punctuation movement; the only additional display expands the existing F.5 premise. The 33 named result headings per language remain. Literal Lean excerpts are relocated unchanged.

The source freeze remains `piv-v12-fb459343d234`, Lean/Mathlib 4.28.0. Its 607 Lean files and separate bounded-gap annex retain their original hashes. **No Lean or Lake rebuild was run.** The final documentary PDFs were compiled and visually checked. Existing publication files and mathematical audit evidence are retained.

The former [v1.23 files](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/01_manuscript), [frozen Lean](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/05_formalization) and [recorded builds](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/03_reproducibility) remain accessible. The new [internal editorial report](02_validation/01_INTERNAL_AUDITS/run_v1.24_editorial_release/10_REPORT/FINAL_INTERNAL_AUDIT_REPORT.md) specifies the verification scope and evidence. [Release integrity](04_integrity/EDITORIAL_v1.24/README.md).

## Resumen de cambios

La versión 1.24 reorganiza la exposición para el lector matemático y separa el detalle de Lean en un complemento. Conserva enunciados, pruebas, constantes, dependencias y atribuciones. La desigualdad desarrollada en F.5 ya existía en la prueba anterior. Se mantiene la puntuación gramatical, situada fuera de las cajas. Los README de I–III se ordenan sin modificar esos artículos. El congelado Lean y sus registros anteriores permanecen idénticos y enlazados; no hubo rebuild. Los nuevos PDF y la auditoría editorial tienen su propio manifiesto.
