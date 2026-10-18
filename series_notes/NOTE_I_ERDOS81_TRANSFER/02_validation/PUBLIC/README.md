# Public validation evidence

`DOCUMENT_BINDINGS.json` and `PDF_QA.json` bind the final English/Spanish Markdown, TeX and PDF files. All listed pages were rendered and inspected. `BILINGUAL_PARITY.json` records normalized mathematical, code-block and link-target parity together with semantic review. `SEMANTIC_DIFF.json` records unchanged displayed mathematics against the prior source hashes.

`FORMAL_SOURCE_EXPORT.json` binds the portable Lean source ZIP. The ZIP and the unpacked `05_formalization/source` tree contain the current source manifest, fresh root/endpoint/full-audit logs and pinned build instructions. `PROOF_BODY_IDENTITY.json` checks every inherited and note-specific Lean file against its prior source bytes; changes are copyright comment prefixes only. Public compiler transcripts remove local filesystem prefixes; original and distributed hashes are both recorded in `COMPILER_LOG_PROVENANCE.json`.

Supplementary finite tests, their explicit domain, negative controls and saved results are in `03_reproducibility`. No private baseline archive, downloaded third-party full text, `.lake` cache or local-only preparation script is part of the publication list.
