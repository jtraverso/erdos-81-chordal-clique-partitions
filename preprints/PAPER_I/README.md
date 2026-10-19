# Paper I — Preprint v1.4

**Affine Profile Reduction for Fractional Triangle Packings in Split Graphs**

Juan Pablo Traverso Gianini · 19 October 2026

The paper reduces a fractional triangle-packing problem on a split graph to pure neighborhood profiles and a three-variable linear program. Its finite consequence is `|E(G)| − 2ν₃*(G) ≤ n²/6 + n/2`.

El artículo reduce un problema de empaquetamiento fraccional de triángulos en un grafo split a perfiles puros de vecindario y un programa lineal de tres variables. Obtiene la cota finita `|E(G)| − 2ν₃*(G) ≤ n²/6 + n/2`.

## Read / Leer

| Language | Document | Typesetting source | Semantic source |
|---|---|---|---|
| EN | [Article PDF](01_manuscript/PAPER_I_preprint_v1.4_en.pdf) | [TeX](01_manuscript/PAPER_I_preprint_v1.4_en.tex) | [Markdown](01_manuscript/PAPER_I_preprint_v1.4_en.md) |
| ES | [Article PDF](01_manuscript/PAPER_I_preprint_v1.4_es.pdf) | [TeX](01_manuscript/PAPER_I_preprint_v1.4_es.tex) | [Markdown](01_manuscript/PAPER_I_preprint_v1.4_es.md) |
| EN | [Formal companion PDF](05_formalization/FORMALIZATION_COMPANION_v1.4_en.pdf) | [TeX](05_formalization/FORMALIZATION_COMPANION_v1.4_en.tex) | [Markdown](05_formalization/FORMALIZATION_COMPANION_v1.4_en.md) |
| ES | [Formal companion PDF](05_formalization/FORMALIZATION_COMPANION_v1.4_es.pdf) | [TeX](05_formalization/FORMALIZATION_COMPANION_v1.4_es.tex) | [Markdown](05_formalization/FORMALIZATION_COMPANION_v1.4_es.md) |

## Place in the series / Lugar en la serie

Papers I–II study fractional profiles and extremizers; III gives an integral split-graph construction; IV establishes chordal bounds and structural stability. V develops the general transfer framework, and VI studies exact local clique partitions. The proof inputs of this paper are unchanged. The numerical estimate is preserved; the affine-profile reduction remains the methodological focus. The finite-duality proof and all orbit boundary cases remain in the article.

La edición actual conserva los resultados y las pruebas, actualiza las relaciones con los artículos posteriores y separa la documentación formal. El artículo matemático y el complemento están disponibles en ambos idiomas.

## Verification, history and citation / Verificación e historia

- [Editorial changelog](CHANGELOG_v1.4.md) and [new internal audit with evidence](02_validation/01_INTERNAL_AUDITS/run_v1.4_editorial_release/10_REPORT/FINAL_INTERNAL_AUDIT_REPORT.md).
- [Unchanged Lean freeze and original verification](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/05_formalization): `lean_v1.2_freeze`. **No Lean/Lake rebuild for this editorial edition.**
- [Previous v1.3 article](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/01_manuscript) and [previous package guide](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/eb335845bfa23375d5040ea31fc4f4b366346287/preprints/PAPER_I/README.md). Historical evidence keeps its original scope.
- [Document reproduction](03_reproducibility/editorial_v1.4/README.md) · [Integrity](04_integrity/EDITORIAL_v1.4/README.md) · [HTML guide](index.html).
- [Historical four-level explanation](PaperI_explained_4_levels.html). Its original publication context is retained; use the current article for updated series references.
- [Deposited editorial edition](https://doi.org/10.5281/zenodo.23478825) · [Series concept DOI](https://doi.org/10.5281/zenodo.21273143) · [Citation](CITATION.cff).

The new review is an AI-assisted internal editorial audit, not independent human peer review, a new Lean build or a new novelty determination. Documents: CC BY-NC 4.0. Existing code, dependency and repository-level license grants remain applicable; see [the series license](../../LICENSE.md).

[Series overview](../../README.md)
