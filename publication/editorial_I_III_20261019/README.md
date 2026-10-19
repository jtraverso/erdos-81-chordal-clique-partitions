# Coordinated editorial release — Papers I–III

19 October 2026. Paper I v1.4, Paper II v1.3, Paper III v1.6. Each has an EN/ES mathematical article and formal companion in Markdown, TeX and PDF. Mathematical content and all 762 frozen Lean files are unchanged; no Lean/Lake build was executed. Individual changelogs and documented internal audits are linked from each paper README.

`RELEASE_CHECKS.json` records navigation, privacy and protected-file checks. Each paper has an incremental integrity manifest; historical manifests remain tied to their original snapshots. The root aggregate SHA-256 index is updated only for changed or new files. The release order is: all three packages pass locally, one coordinated GitHub content update, one Zenodo collection version, then a final GitHub metadata and manifest update.

The comparison code is archived below; its input layout is the local editorial staging tree (`baseline/PAPER_I_en.md`, `edition/PAPER_I/01_manuscript`, `edition/PAPER_I/05_formalization`, etc.). All inputs, protected-expression indices and exact diffs are separately included in the individual audit packages. Run each package's `verify_editorial.py` for final hash and frozen-tree verification without reconstructing staging.
