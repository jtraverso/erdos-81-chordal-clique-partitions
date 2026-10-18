# Internal publication audit — Preprint 1.0

Juan Pablo Traverso Gianini · 18 October 2026

**Verdict: PASS for the documented publication checks.** The frozen scope comprises
Paper V, Paper VI, Series Notes I–II, and one separate formalization companion for
each work, in English and Spanish. This is an internal technical and editorial
audit, not independent human peer review or a certification of historical priority.

## Manuscripts and export chain

The release contains 48 current manuscript/companion files in Markdown, LaTeX and
PDF. All 16 PDFs (165 pages) have final edition labels, compilation evidence,
rendered-page inspection records and SHA-256 bindings. Text extraction checks found
no draft labels, unresolved placeholders, workstation paths or text outside the page.
The per-work records document the final rendered pages; the PDF export check is
complementary to visual inspection.

The cross-review checked hypotheses, attribution and bilingual mathematical parity.
The supplied review observations are addressed in [the response](REVIEW_RESPONSE.md).
Paper IV's all-order bound with an absolute additive constant is distinguished from
its sharp eventual bound. The unavailable detailed AUDIT2 reports are not claimed
to have been audited; the concrete findings supplied in the conversation were addressed.

## Lean source freezes

| Work | Imported local modules | Local declarations audited | Declarations visited | Nonstandard axioms |
|---|---:|---:|---:|---:|
| Paper V | 122 | 2838 | 5547 | 0 |
| Paper VI | 79 | 1836 | 3421 | 0 |
| Note I | 324 | 6850 | 10304 | 0 |
| Note II | 343 | 7393 | 10976 | 0 |

These scopes overlap; the rows must not be summed as independent declarations.
The final builds and interface checks pass. Paper V's ten statement/axiom checks
contain 403 type queries and 431 axiom queries, including the concrete copy-packing
and mixed-copy interfaces. The transitive audits admit only the standard Lean
foundations `propext`, `Classical.choice` and `Quot.sound`. No additional mathematical
axiom is used. The companions identify canonical entry points, pinned Mathlib,
exact theorem correspondences, archive hashes and reproduction commands.

Full Apache-2.0 licenses and ownership notices accompany the author's software;
existing upstream notices remain. The documents use CC BY-NC 4.0.

## Finite computational evidence

Paper V includes the current SEAL code and variants, 218 saved physical-output
checks (110 Python, 54 JavaScript, 54 C++), 38 exact rational duals and seven negative
controls. The N1 regression covers 685 initial states and 27,708 operation trials;
the reference suite contains 30 saved certificates. The separate BK checker verifies
70 saved optima, the dual value 19/2 and beta=2, and rejects a modified dual price.
Scalar Certo checks and their stated counterexample controls are retained.

Paper VI includes 33 literal-graph checks, main and recourse certificates and
negative controls. The notes' exact-arithmetic scripts were rerun from the public
packages. Their deterministic saved result bytes agree. Relocation records distinguish
regenerated neutral-directory certificates from redacted execution metadata.
None of these finite checks is presented as a proof of a universal statement.

## Packaging, privacy and navigation

The static audit checks all current document filenames, software licenses, proof
escape hatches, archive privacy, GitHub file-size limits and local navigation.
Public packages contain no credentials or personal workstation paths. The secret
credential is stored outside the repositories. The new release was assembled from
hash-verified allowlists; caches, private orchestration and third-party article PDFs
were excluded. The 13,987 previously published scientific files of Papers I–IV
retain their checked bytes.

Five HTML pages pass source-structure and local-link checks. Browser screenshot
capture was blocked by tool policy; browser-rendered HTML verification is not claimed.
The PDF visual checks are unaffected.

The root `manifest_sha256.txt` and per-work `04_integrity` manifests identify the
public bytes. Run `python publication/preprint1.0/verify_release.py` from the root
to verify the complete series manifest. Its own manifest file is excluded from
that manifest to avoid a circular hash.

## Evidence index

- [Static publication audit](STATIC_AUDIT.json)
- [Sixteen PDF exports](PDF_EXPORT_CHECK.json)
- [HTML source and local links](HTML_CHECK.json)
- [Cross-review](CROSS_REVIEW_FINAL.md)
- [Final assembly review](ASSEMBLY_REVIEW.md)
- [Previous release preservation](PREVIOUS_RELEASE_PRESERVATION.json)
- [Note arithmetic replay](NOTE_ARITHMETIC_REPLAY.json)

Per-work `02_validation` directories contain the remaining logs, semantic comparisons,
rendered evidence and source receipts. The manuscripts do not claim that computational
checks or Lean checking establish priority or replace specialist mathematical review.
