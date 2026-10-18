# Clique partitions and chordal structure â€” Papers Iâ€“VI

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21273143.svg)](https://doi.org/10.5281/zenodo.21273143)

This repository contains Juan Pablo Traverso Gianini's preprint series,
formal sources and verification evidence concerning
[ErdÅ‘s Problem #81](https://www.erdosproblems.com/81).

## Papers Vâ€“VI and series notes â€” Preprint 1.0

The series continues with new questions about resource-dominated packing relaxations, realizability, exact local clique partitions and stability. ErdÅ‘s #81 supplies the context; these new works do not claim another priority result for that bound.

| Work | Publication package |
|---|---|
| Paper V | [Colorability and Realizability Defects](preprints/PAPER_V/README.md) |
| Paper VI | [Optimal Clique Partitions under Local Perturbations](preprints/PAPER_VI/README.md) |
| Series Note I | [Transfer and the ErdÅ‘s 81 bound](series_notes/NOTE_I_ERDOS81_TRANSFER/README.md) |
| Series Note II | [Exact chordal stability](series_notes/NOTE_II_CHORDAL_STABILITY/README.md) |

Each package contains English and Spanish manuscripts in Markdown, LaTeX and PDF, an HTML explanation, a separate formalization companion, Lean sources, licenses and reproducibility evidence. [Publication index](PUBLICATION_INDEX.json).

[Internal publication audit and evidence](publication/preprint1.0/INTERNAL_AUDIT_FINAL.md) · [Response to the supplied review](publication/preprint1.0/REVIEW_RESPONSE.md).

## Explore the series

- [Papers Iâ€“VI and notes: bilingual explanations at different levels](index.html)
- [HTML preview of the series](https://htmlpreview.github.io/?https://github.com/jtraverso/erdos-81-chordal-clique-partitions/blob/main/index.html)

## arXiv endorsement

I am preparing to submit this preprint series to arXiv (math.CO) and, as a first-time submitter, I
need an endorsement. If you are an arXiv author eligible to endorse in math.CO, have looked at
these papers, and found that they add value and are appropriate for the category, you can endorse
me at https://arxiv.org/auth/endorse?x=N8V4R6 (endorsement code `N8V4R6`). An endorsement only confirms that the work is suitable for
the subject area; it is not a review or an approval of its results. Thank you.

*En espaÃ±ol:* preparo el envÃ­o de esta serie de preprints a arXiv (math.CO) y, como es mi primer
envÃ­o, necesito un endorsement. Si eres autor de arXiv habilitado para dar endorsement en math.CO,
revisaste estos trabajos y te parece que aportan y son adecuados para la categorÃ­a, puedes dÃ¡rmelo
en https://arxiv.org/auth/endorse?x=N8V4R6 (cÃ³digo `N8V4R6`). El endorsement solo confirma que el trabajo es adecuado para el Ã¡rea;
no es una revisiÃ³n ni una aprobaciÃ³n de sus resultados. Â¡Gracias!

## Paper IV â€” v1.23 editorial revision

**Clique partitions with rooted simplicial defect: quantitative stability and
sharp eventual bounds.** Version 1.23 moves administrative history out of the
manuscript and adds a bilingual explainer. Mathematical content and the Lean
freeze are unchanged from the published v1.22, whose consolidated external
review is **PASS, E0â€“E8, zero open corrective actions**. The v1.23 documentary
checks are separate. This release is authorized for GitHub publication;
its published Zenodo snapshot is 10.5281/zenodo.23089131.

- [English PDF](preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_en.pdf)
- [Spanish PDF](preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.23_es.pdf)
- [Paper IV explained at four levels](preprints/PAPER_IV/PaperIV_explained_4_levels.html)
- [Editorial changelog](preprints/PAPER_IV/CHANGELOG_v1.23.md)
- [Paper IV: scope, package and limits](preprints/PAPER_IV/README.md)
- [Consolidated external PASS](preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md)
- [English translation of the consolidated report](preprints/PAPER_IV/02_validation/translations/v1.22_r4/FINAL_CONSOLIDATED_AUDIT_REPORT_en.md)
- [Frozen Lean sources](preprints/PAPER_IV/05_formalization/README.md)
- [Superseded public draft v0.8](preprints/PAPER_IV/superseded/README.md)
- [Publication integrity checks](preprints/PAPER_IV/04_integrity/PUBLICATION_CHECKS.json)

The paper proves the all-orders chordal bound câ‚„(G) â‰¤ floor(n(n+1)/6) + b
for an absolute constant, and the sharp eventual maximum. It also treats
rooted simplicial defect, quantitative same-root stability of graphs and
partitions, and explicit (impractical) thresholds. See the manuscript for exact
hypotheses and attribution. Neither universal b = 0 nor priority for the
extremal bound is claimed.

## Papers Iâ€“III

| Paper | Current preprint | Scope |
| --- | --- | --- |
| [I](preprints/PAPER_I/README.md) | v1.3 â€” Affine Profile Reduction for Fractional Triangle Packings in Split Graphs | Finite fractional triangle-packing bound for split graphs |
| [II](preprints/PAPER_II/README.md) | v1.2 â€” Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs | Exact fractional-cover extremum on chordal graphs |
| [III](preprints/PAPER_III/README.md) | v1.5 â€” Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing | Integral split-graph bound with sharp quadratic coefficient 1/6 |

Their released packages and historical audits are unchanged. Each paper has
its own English and Spanish manuscripts, source freeze and verification
evidence. Earlier verdicts do not substitute for Paper IV's audit.

## Formal verification and limits

Paper IV uses source identity `piv-v12-fb459343d234`: 607 Lean modules and
615 source/configuration entries. The verified external build checked 607
modules, 19 targets and 224 publication exports, plus a separate 50-module
annex. Later editorial reviews inherited that evidence by checked identity;
they did not rerun the kernel. Audited axiom footprints use only propext,
Classical.choice and Quot.sound, or subsets.

Lean, Mathlib and their pinned dependencies remain third-party software.
These preprints are not human peer-reviewed. The external AI report discloses
the same model family, continuation of its audit session and shared
machine/cache. The mandatory supplemental log verifier remains part of
reproduction. No claim of bibliographic originality follows from a cone check.

## Citation, integrity and licenses

Use [CITATION.md](CITATION.md), [CITATION.bib](CITATION.bib) or
[CITATION.cff](CITATION.cff). The series concept DOI remains
[10.5281/zenodo.21273143](https://doi.org/10.5281/zenodo.21273143).
The existing [Papers Iâ€“III deposit](https://doi.org/10.5281/zenodo.22064657)
does not include Paper IV. The published v1.22 is tagged `paper-IV-v1.22`,
commit `cfcd5cf57cadc8583a218caaa1476911efe6158a`.
The published Iâ€“IV snapshot is [10.5281/zenodo.23089131](https://doi.org/10.5281/zenodo.23089131), verified through the Zenodo API on 18 October 2026. It contains the eight English and Spanish PDFs of Iâ€“IV, including Paper IV v1.23. The evolving collection keeps the concept DOI above.

The root `manifest_sha256.txt` covers the prepared repository except itself
and Git metadata. Paper IV has its own manifest and verification procedure.
Earlier Paper IV manuscripts required by the audit, including published
v1.22, are retained as audit backups rather than alternative current editions;
the public v0.8 draft is preserved as superseded.

Documents follow CC BY-NC 4.0; see [LICENSE.md](LICENSE.md). Author-owned software in the new Vâ€“VI and notes release is Apache-2.0; package notices distinguish inherited third-party material. Existing upstream
software licenses remain applicable; packaging does not relicense Mathlib
or separately licensed Lean Pool/Mathlib contributions.
The original Paper III `Ax2` Lean sources are also available under Apache-2.0
through the author's [specific source-code grant](LEAN_SOURCE_APACHE_2_0_GRANT.md);
this exception does not change the license of the papers or audit artifacts.
