# Erdős Problem #81 — Chordal Clique Partitions

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21273143.svg)](https://doi.org/10.5281/zenodo.21273143)

This repository contains Juan Pablo Traverso Gianini's preprint series,
formal sources and verification evidence concerning
[Erdős Problem #81](https://www.erdosproblems.com/81).

## Paper IV — v1.22 selected for publication

**Clique partitions with rooted simplicial defect: quantitative stability and
sharp eventual bounds.** The selected bilingual manuscripts are exactly those
approved by external adversarial review **v1.22-r4: PASS, E0–E8, zero open
corrective actions**. This local preparation does not publish, tag or deposit
anything; the author must approve those actions separately.

- [English PDF](preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.22_en.pdf)
- [Spanish PDF](preprints/PAPER_IV/01_manuscript/PAPER_IV_preprint_v1.22_es.pdf)
- [Paper IV: scope, package and limits](preprints/PAPER_IV/README.md)
- [Consolidated external PASS](preprints/PAPER_IV/02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/30_REPORT/FINAL_CONSOLIDATED_AUDIT_REPORT.md)
- [Frozen Lean sources](preprints/PAPER_IV/05_formalization/README.md)
- [Superseded public draft v0.8](preprints/PAPER_IV/superseded/README.md)
- [Publication integrity checks](preprints/PAPER_IV/04_integrity/PUBLICATION_CHECKS.json)

The paper proves the all-orders chordal bound c₄(G) ≤ floor(n(n+1)/6) + b
for an absolute constant, and the sharp eventual maximum. It also treats
rooted simplicial defect, quantitative same-root stability of graphs and
partitions, and explicit (impractical) thresholds. See the manuscript for exact
hypotheses and attribution. Neither universal b = 0 nor priority for the
extremal bound is claimed.

## Papers I–III

| Paper | Current preprint | Scope |
| --- | --- | --- |
| [I](preprints/PAPER_I/README.md) | v1.3 — Affine Profile Reduction for Fractional Triangle Packings in Split Graphs | Finite fractional triangle-packing bound for split graphs |
| [II](preprints/PAPER_II/README.md) | v1.2 — Complete-Split Extremizers for a Fractional Triangle-Cover Functional on Chordal Graphs | Exact fractional-cover extremum on chordal graphs |
| [III](preprints/PAPER_III/README.md) | v1.5 — Linear-Error Clique Partitions of Split Graphs via Structured Triangle Packing | Integral split-graph bound with sharp quadratic coefficient 1/6 |

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
The existing [Papers I–III deposit](https://doi.org/10.5281/zenodo.22064657)
does not include this prospective four-paper package. No new version DOI,
publication date or release commit is assigned here.

The root `manifest_sha256.txt` covers the prepared repository except itself
and Git metadata. Paper IV has its own manifest and verification procedure.
Intermediate Paper IV versions are retained only as audit inputs, not
alternative releases; the public v0.8 draft is preserved as superseded.

Documents follow CC BY-NC 4.0; see [LICENSE.md](LICENSE.md). Existing upstream
software licenses remain applicable; packaging does not relicense Mathlib
or separately licensed Lean Pool/Mathlib contributions.
