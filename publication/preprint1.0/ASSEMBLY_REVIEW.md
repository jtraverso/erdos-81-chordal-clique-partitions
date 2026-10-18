# Final assembly cross-review — Preprint 1.0

**Status: PASS — static internal links, package licenses, and the final Paper V companion delta.**

This independent read-only review inspected 66 current Markdown, TeX, README, license and HTML files and resolved 213 internal links, including public GitHub links pointing back to this repository. Every checked destination now exists. It did not open a browser, execute Lean, rebuild documents, or inspect PDF pages. Exact input hashes and link results are in `ASSEMBLY_REVIEW.json`.

## Internal links and package structure

The previously pending Paper V formal directory and both canonical companion PDFs are now present. All nine formerly unresolved occurrences now resolve. The current manuscript and source links, six V figure resources, the four work-level README/HTML pages and their formalization/integrity links resolve in the assembled repository.

All four `04_integrity/` directories exist, and the documented verifier exists at `publication/preprint1.0/verify_release.py`. The amended bilingual Note II HTML states sufficiently large n, defines d=M(n)−cp(G), and requires 0≤d≤n/2000.

## Licenses

All four work directories provide a document-license notice and the full Creative Commons Attribution-NonCommercial 4.0 text. All four formal source trees now provide the full Apache 2.0 text. Paper V's `05_formalization/lean/LICENSES/NOTICE.md` retains third-party notices and mathematical attribution; the notes' NOTICE files explicitly cover enumerated author-owned inherited source cuts. No new license is inferred for third-party material beyond its preserved notices.

## Final Paper V companion delta

Both final companions were compared to the exact byte hashes recorded by the preceding content review. Reversing only the six documented substitutions per language recovers those earlier hashes exactly. This supplies a complete byte-level delta check, rather than merely a rereading of selected paragraphs.

The substitutions update 121→122 public modules, 2581→2582 build jobs, 2832/121/5541→2838/122/5547 declaration/module/visited counts, and the previous query summary to 403 type queries plus 431 axiom queries. Two editorial substitutions rename the correspondence row as supporting interfaces and name the actual validation directory. No theorem statement, hypothesis, SEAL limitation, attribution, or mathematical claim changes in this final delta. `COMPANION_V_FINAL_DELTA_CHECK.json` records the exact substitutions and current/prior hashes.

## Boundary of this PASS

The earlier manifest snapshot passed entry-wise verification, but it preceded final Paper V integration. Its results are retained only as historical observations in the JSON. Final manifests must be regenerated and checked by the assembler; this review deliberately does not certify the obsolete manifests after additional files were copied.

A separate known publication-hygiene task concerns personal paths in eight compiler logs. The responsible agent is sanitizing them. That task does not alter the link/license or companion-delta conclusions here, but must close before public release. This report is not an unrestricted release approval and makes no claim that every compiler log has already been sanitized.

No manuscript, source file, or publication page was modified by this review.
