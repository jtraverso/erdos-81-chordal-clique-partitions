# Reproducing the editorial documents

The supplied final TeX files produce the published PDFs. From each file's directory run `tectonic --keep-logs FILE.tex` (or use the script below with `TECTONIC` set to your executable). Resolve the font/type resources according to their existing licenses. The companion reuses the same Segoe UI Symbol resource as the previous article; this revision grants no new rights over that resource. A full checkout contains the article figures and typesetting resources. The release records exact PDF hashes; a different TeX/runtime version may yield different PDF bytes.

`python compile_documents.py PATH_TO_PAPER_IV` compiles the four v1.24 documents only. It does not invoke Lean or Lake. The publication audit and compiler logs live under `02_validation/01_INTERNAL_AUDITS/run_v1.24_editorial_release/`.

The final TeX is the checked rendering source. Markdown remains the readable source. No unattended Markdown conversion is claimed to preserve the custom typesetting of literal Lean excerpts. The frozen formal-source reproduction procedure remains in the preceding `03_reproducibility/README.md`; it was not executed for this editorial revision.
