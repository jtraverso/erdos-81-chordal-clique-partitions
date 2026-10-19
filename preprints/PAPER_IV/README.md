# Paper IV — quantitative stability and sharp eventual bounds

**Clique partitions with rooted simplicial defect: quantitative stability and sharp eventual bounds**  
Juan Pablo Traverso Gianini · Preprint v1.24.1 · 19 October 2026

## Read / Leer

| Document | PDF | TeX | Markdown |
|---|---|---|---|
| Article / Artículo — EN | [PDF](01_manuscript/PAPER_IV_preprint_v1.24.1_en.pdf) | [TEX](01_manuscript/PAPER_IV_preprint_v1.24.1_en.tex) | [MD](01_manuscript/PAPER_IV_preprint_v1.24.1_en.md) |
| Article / Artículo — ES | [PDF](01_manuscript/PAPER_IV_preprint_v1.24.1_es.pdf) | [TEX](01_manuscript/PAPER_IV_preprint_v1.24.1_es.tex) | [MD](01_manuscript/PAPER_IV_preprint_v1.24.1_es.md) |
| Formal companion / Complemento formal — EN | [PDF](05_formalization/FORMALIZATION_COMPANION_v1.24_en.pdf) | [TEX](05_formalization/FORMALIZATION_COMPANION_v1.24_en.tex) | [MD](05_formalization/FORMALIZATION_COMPANION_v1.24_en.md) |
| Formal companion / Complemento formal — ES | [PDF](05_formalization/FORMALIZATION_COMPANION_v1.24_es.pdf) | [TEX](05_formalization/FORMALIZATION_COMPANION_v1.24_es.tex) | [MD](05_formalization/FORMALIZATION_COMPANION_v1.24_es.md) |

[Navigation-only patch v1.24.1](CHANGELOG_v1.24.1.md) · [Patch audit](02_validation/01_INTERNAL_AUDITS/run_v1.24.1_navigation/REPORT.md) · [Web overview](index.html) · [Explanation at four levels](PaperIV_explained_4_levels.html) · [Changelog v1.23→v1.24](CHANGELOG_v1.24.md)

Article v1.24.1 corrects only the portable link to the formal companion and the title-page version. The companion remains v1.24, byte-identical. El artículo v1.24.1 solo corrige el enlace portable y su identificador de versión; el complemento formal v1.24 y el Lean no cambian.

## Contribution and place in the series

Near equality in clique partition bounds forces graph structure and constrains all near-optimal partitions through the same retained clique root. The paper proves quantitative stability for fixed rooted simplicial defect and a uniform sublinear-defect statement. For chordal graphs, the order-four partition bound is M(n)+b at every order and M(n) for sufficiently large n, where M(n)=floor(n(n+1)/6). It does not assert b=0 at every order.

The construction uses the fractional and rounding infrastructure developed in Papers I–III. Papers V–VI and the series notes study realizability, local exact formulas and related stability. Attributions to the other solutions and structural antecedents remain in the manuscript; this editorial revision makes no new mathematical or priority claim.

En español: el artículo estudia la estructura que impone la casi igualdad y conserva una misma raíz para controlar el grafo y sus particiones casi óptimas. La cota cordal es M(n)+b a todo orden y M(n) para órdenes suficientemente grandes. La versión 1.24 cambia la exposición y separa el complemento formal; no altera la matemática.

## Formalization and validation

The [source freeze](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/05_formalization) remains `piv-v12-fb459343d234`, Lean/Mathlib 4.28.0: 607 main Lean files and a separate bounded-gap annex. The [historical build evidence](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/03_reproducibility) remains the evidence for kernel checking. **No Lean/Lake rebuild accompanied this editorial release.**

The [new internal editorial audit](02_validation/01_INTERNAL_AUDITS/run_v1.24_editorial_release/10_REPORT/FINAL_INTERNAL_AUDIT_REPORT.md) passes within its declared scope, with document hashes, semantic comparisons, source identity checks and rendered-page evidence. It is AI-assisted internal review, not human peer review. The [earlier external audit report](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md) applies to its original snapshot and is not relabeled as a new audit.

[Deposited article v1.24.1 and companion v1.24](https://doi.org/10.5281/zenodo.23479507) · [Current coordinated release](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/releases/tag/series-editorial-2026-10-19).

## Reproduction, history and citation

- [Patch integrity](04_integrity/EDITORIAL_v1.24.1/README.md). Compile the two supplied v1.24.1 TeX files with `tectonic --keep-logs` from `01_manuscript/`; no Lean/Lake command is required.
- [Document-only reproduction](03_reproducibility/editorial_v1.24/README.md) and [editorial release manifest](04_integrity/EDITORIAL_v1.24/README.md).
- [Previous v1.23 edition](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ef31294ad67dfe3f44bc47cec4791c836f55e8aa/preprints/PAPER_IV/01_manuscript); [previous changelog](CHANGELOG_v1.23.md). Old files, reports and manifests are retained.
- [Earlier deposited edition containing Paper IV v1.24](https://doi.org/10.5281/zenodo.23476768); [series concept DOI](https://doi.org/10.5281/zenodo.21273143); [preceding I–IV deposit](https://doi.org/10.5281/zenodo.23089131). Cite the version used: [CITATION.cff](CITATION.cff).
- Documents follow [CC BY-NC 4.0](LICENSE.md); software and reused resources retain their existing notices and licenses.

[Series overview](../../README.md)
