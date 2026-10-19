# Paper III — Preprint v1.5

**Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing**  
Juan Pablo Traverso Gianini · 23 August 2026

| Language | Manuscript | Typesetting source | Semantic source | Formal sources |
|---|---|---|---|---|
| EN | [PDF](01_manuscript/PAPER_III_preprint_v1.5_en.pdf) | [TeX](01_manuscript/PAPER_III_preprint_v1.5_en.tex) | [Markdown](01_manuscript/PAPER_III_preprint_v1.5.md) | [Lean and evidence](05_formalization/) |
| ES | [PDF](01_manuscript/PAPER_III_preprint_v1.5_es.pdf) | [TeX](01_manuscript/PAPER_III_preprint_v1.5_es.tex) | [Markdown](01_manuscript/PAPER_III_preprint_v1.5_es.md) | [Lean and evidence](05_formalization/) |

For split graphs, the paper constructs edge-disjoint triangles with `|E(G)| − 2ν₃(G) ≤ n²/6 + Cn`, for an absolute constant C. Completing uncovered edges gives a clique partition at the same scale. The quadratic coefficient 1/6 is sharp; the least linear coefficient is not determined.

Para grafos split, el artículo construye triángulos disjuntos por aristas con `|E(G)| − 2ν₃(G) ≤ n²/6 + Cn`, para una constante absoluta C. Completar las aristas restantes produce una partición en cliques a la misma escala. El coeficiente cuadrático 1/6 es óptimo; no se determina el menor coeficiente lineal.

## Place in the series / Lugar en la serie

The proof treats the bulk and extremal corridors separately, combining fractional margin with explicit constructions. Its nibble infrastructure is reused in Paper IV. The split-graph result alone does not imply the full chordal result.

The manuscripts retain their original publication context. References in them to the full chordal problem as open describe that earlier stage; [Paper IV](../PAPER_IV/README.md) contains the subsequent bound and structural results. The manuscript and Lean versions of this paper have not changed in the present navigation update.

Los manuscritos conservan su contexto de publicación original. Las menciones al problema cordal completo como abierto corresponden a esa etapa; [Paper IV](../PAPER_IV/README.md) contiene la cota posterior y los resultados estructurales. Esta actualización del README no modifica el manuscrito ni sus fuentes Lean.

## Reading and verification / Lectura y verificación

- [Bilingual explanation at four levels](PaperIII_explained_4_levels.html).
- [Recorded final external AI-audit report](02_validation/02_IA_ADVERSARIAL_AUDITS/run_2026-08-23_v1.5_residual_closure/30_REPORT/FINAL_CLOSURE_REPORT.md).
- [Formal source package and its recorded evidence](05_formalization/).
- [Reproduction records](03_reproducibility/) · [Integrity manifests](04_integrity/).
- [Previous README, including the full release and audit history](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_III/README.md).
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

The author-owned `Ax2` sources also have the [specific Apache-2.0 source-code grant](../../LEAN_SOURCE_APACHE_2_0_GRANT.md). The frozen source archive remains SHA-256 `79ee24c38fd776bc2585a0c3c996e30817f0829fc5064463bdbde0fa2d3d7104`.
