# Internal editorial audit — Paper IV v1.24.1

**EDITORIALLY_READY / PASS within the navigation-patch scope.** 19 October 2026. Internal AI-assisted review by OpenAI Codex; not human peer review or a new kernel audit.

## Evidence and checks

- Exact reverse-transform equality: each new MD/TeX source becomes byte-identical to v1.24 by reverting only the version token and reference [24] URL. See the four exact diffs. Mathematical text, displayed and inline formulas, hypotheses, references and proof steps are otherwise unchanged.
- Both final TeX sources compiled successfully. No overfull boxes, missing glyphs or undefined control sequences. The existing harmless fontconfig warning and Spanish underfull-box notice remain.
- All 124 pages (61 EN, 63 ES) rendered and compared to v1.24. Exactly 120 pages have identical pixel data. Four changed pages were visually inspected at readable resolution: the two title pages and two last reference pages. No clipping, missing content or layout regression. The bibliography link changes color from a file action to a web link; text and layout are preserved.
- PDF text extraction matches v1.24 exactly after replacing the front-matter 1.24.1 token with 1.24. This agrees with exact source preservation; extraction alone is not the semantic proof.
- Reference [24] is now a public HTTPS URI pinned to the unchanged companion. No external-file PDF action remains in either article. The target objects exist in the published baseline commit.
- Companion v1.24, historical article v1.24, source freezes, toolchains and Lean files are excluded from changes. Release checks verify the protected paths and hashes.

`DOCUMENT_CHECKS.json` binds sources, PDFs, per-page rendering hashes and compiler logs. `visual/` contains the four inspected changed pages. `AUDIT_PLAN.md` and the source diffs define the strict scope. Navigation, publication files and manifests are checked in the separate series closure record.

No open editorial findings within this patch. Final distribution verification is recorded in the Zenodo and GitHub release receipts; this report does not assert a publication action before it happens.

En español: auditoría interna de los dos documentos afectados, con preservación exacta de fuente salvo versión/enlace, comparación de las 124 páginas y revisión visual de las cuatro páginas cambiadas. No se ha ejecutado Lean/Lake ni renovado la revisión matemática.
