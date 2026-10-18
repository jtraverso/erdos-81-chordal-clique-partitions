# Paper VI Preprint 1.0 — document reproduction

The English and Spanish Markdown files are the semantic sources; the supplied standalone TeX files record the typesetting source. Their mathematical displays are protected by MATHEMATICAL_SEMANTIC_DIFF.json. Typesetting used Pandoc 3.11 and Tectonic, with the series layout embedded in each TeX file. No external figures or private source files are required.

From each document directory, run Tectonic twice on the relevant TeX file, for example:

```
tectonic --keep-logs PAPER_VI_preprint_v1.0_en.tex
tectonic --keep-logs PAPER_VI_preprint_v1.0_en.tex
```

Use the corresponding `_es.tex` file for Spanish. In `05_formalization/`, run the same two passes on `FORMALIZATION_COMPANION_v1.0_en.tex` and its Spanish counterpart. Rendering and visual-review records bind the supplied PDF bytes and every page image; recompilation can change PDF metadata and must receive its own document hash and visual-review record.

The proof package is reproduced independently using its pinned Lean toolchain and the commands in the companion. PDF generation does not verify a mathematical proof, and finite certificates do not replace universal proofs.
