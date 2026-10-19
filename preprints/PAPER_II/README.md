# Paper II — Preprint v1.2

**Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs**  
Juan Pablo Traverso Gianini · 22 August 2026

| Language | Manuscript | Typesetting source | Semantic source | Formal sources |
|---|---|---|---|---|
| EN | [PDF](01_manuscript/PAPER_II_preprint_v1.2_en.pdf) | [TeX](01_manuscript/PAPER_II_preprint_v1.2_en.tex) | [Markdown](01_manuscript/PAPER_II_preprint_v1.2.md) | [Lean and evidence](05_formalization/) |
| ES | [PDF](01_manuscript/PAPER_II_preprint_v1.2_es.pdf) | [TeX](01_manuscript/PAPER_II_preprint_v1.2_es.tex) | [Markdown](01_manuscript/PAPER_II_preprint_v1.2_es.md) | [Lean and evidence](05_formalization/) |

For every integer `n ≥ 1`, the maximum of `|E(G)| − 2τ₃*(G)` over chordal graphs of order n is `floor((2n+1)²/24)`. A complete-split graph attains it. The proof uses admissible vertex copies and a finite calculation on complete-split graphs.

Para cada entero `n ≥ 1`, el máximo de `|E(G)| − 2τ₃*(G)` entre los grafos cordales de orden n es `floor((2n+1)²/24)`, alcanzado por un grafo completo-split. La prueba utiliza copias admisibles de vértices y un cálculo finito en la familia terminal.

## Place in the series / Lugar en la serie

The result identifies a fractional extremum; obtaining an integral partition requires an additional construction. Its copy mechanism informs the mixed structural arguments of Paper IV, whose integral conclusions have their own proofs.

The manuscripts retain their original publication context. References in them to the full chordal problem as open describe that earlier stage; [Paper IV](../PAPER_IV/README.md) contains the subsequent bound and structural results. The manuscript and Lean versions of this paper have not changed in the present navigation update.

Los manuscritos conservan su contexto de publicación original. Las menciones al problema cordal completo como abierto corresponden a esa etapa; [Paper IV](../PAPER_IV/README.md) contiene la cota posterior y los resultados estructurales. Esta actualización del README no modifica el manuscrito ni sus fuentes Lean.

## Reading and verification / Lectura y verificación

- [Bilingual explanation at four levels](PaperII_explained_4_levels.html).
- [Recorded final external AI-audit report](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-21_v1.2_pkgfix/30_REPORT/FINAL_AUDIT_REPORT.md).
- [Formal source package and its recorded evidence](05_formalization/).
- [Reproduction records](03_reproducibility/) · [Integrity manifests](04_integrity/).
- [Previous README, including the full release and audit history](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_II/README.md).
- [Papers I–III deposited edition](https://doi.org/10.5281/zenodo.22064657) · [Series concept DOI](https://doi.org/10.5281/zenodo.21273143).

The recorded AI-assisted audits are distinct from human peer review. Their scope, build targets and axiom checks are documented in the linked evidence. This README update does not perform a new Lean build or assert a new determination of historical priority.

Las auditorías asistidas por IA se distinguen de la revisión humana por pares. Su alcance, compilaciones y comprobaciones de axiomas figuran en las evidencias enlazadas. Esta actualización no ejecuta Lean ni formula una nueva reclamación de prioridad.

## Package / Estructura

`01_manuscript/`: published English and Spanish manuscripts, figures and hashes.  
`02_validation/`: internal and external AI-audit reports.  
`03_reproducibility/`: reproduction instructions and recorded builds.  
`04_integrity/`: original release manifests and provenance.  
`05_formalization/`: unchanged frozen Lean sources and verification evidence.  
`superseded/`: historical packages, with their original status retained.

Documents: CC BY-NC 4.0. Existing source and dependency licenses remain applicable; see the [series license](../../LICENSE.md). This navigation revision does not relicense any material.
