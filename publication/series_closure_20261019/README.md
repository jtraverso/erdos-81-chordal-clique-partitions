# Series distribution closure — 19 October 2026

**PASS: NAV-01, NAV-02 and NAV-03 closed.** Internal AI-assisted documentary audit, not a new mathematical, kernel or human peer review.

| Finding | Resolution | Evidence |
|---|---|---|
| NAV-01: Paper IV standalone companion link | Article v1.24.1 uses a public commit-pinned HTTPS link; companion v1.24 remains identical | [Patch audit](../../preprints/PAPER_IV/02_validation/01_INTERNAL_AUDITS/run_v1.24.1_navigation/REPORT.md) |
| NAV-02: latest GitHub release omitted I–III editions | Coordinated release includes all 32 current PDFs plus SHA-256 manifest, and is Latest | [Release receipt](GITHUB_RELEASE_RECEIPT.json) |
| NAV-03: ambiguous current-collection label | Paper IV README distinguishes earlier v1.24 deposit, current v1.24.1 edition and series DOI | [Current package guide](../../preprints/PAPER_IV/README.md) |

[Current GitHub release](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/releases/tag/series-editorial-2026-10-19) · [Zenodo collection 9](https://doi.org/10.5281/zenodo.23479507) · [Verified public deposit](../zenodo/v9_23479507/PUBLIC_RECEIPT.json).

Current articles: I 1.4, II 1.3, III 1.6, IV 1.24.1; V–VI and Notes I–II 1.0. Paper IV companion stays 1.24; other companions match their article versions. All 96 MD/TeX/PDF artifacts are present. All 32 public Zenodo PDFs match the repository bytes and the SHA-256 digests of GitHub release assets. All PDF front pages have the expected version; no external-file PDF action remains. The series DOI resolves to collection 9. Historical records and releases remain available.

`FINAL_AUDIT.json` records the current-series checks, including 316 relative navigation links. `CHECKS.json` verifies exact source deltas, protected paths, changed-file navigation and privacy. The [patch changelog](../../preprints/PAPER_IV/CHANGELOG_v1.24.1.md) and [incremental manifest](../../preprints/PAPER_IV/04_integrity/EDITORIAL_v1.24.1/SHA256SUMS.txt) distinguish documentary changes from unchanged mathematics, Lean and prior evidence.

No open findings in this distribution scope. No Lean/Lake build or mathematical change. The prior statement of no new human peer review remains unchanged. En español: los tres pendientes de distribución están cerrados y comprobados; los resultados y congelados Lean permanecen intactos.
