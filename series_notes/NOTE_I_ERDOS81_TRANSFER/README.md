# Series research note I — Preprint 1.0

Juan Pablo Traverso Gianini · 18 October 2026

This separate note reorganizes part of Paper IV through Paper V’s realizable-class transfer interface. It does not claim a new solution of Erdős Problem 81 or a mathematically independent proof. The eventual sharp bound and all-orders additive bound retain IV’s structural and rounding inputs.

## Manuscripts

- [English PDF](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_en.pdf) · [Markdown](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_en.md) · [TeX](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_en.tex).
- [PDF español](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_es.pdf) · [Markdown](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_es.md) · [TeX](01_manuscript/ERDOS81_TRANSFER_NOTE_v1.0_es.tex).

## Formal companion and sources

- [English companion](05_formalization/FORMALIZATION_COMPANION_v1.0_en.pdf) and [companion español](05_formalization/FORMALIZATION_COMPANION_v1.0_es.pdf); editable MD/TeX accompany both.
- [Portable source archive](05_formalization/formal_sources/NOTE_I_LEAN435_FINAL_SOURCE_v1.0.zip).
- [Source project and reproduction instructions](05_formalization/source/SOURCE_REPRODUCTION.md).
- [Final source validation](05_formalization/source/FINAL_FORMAL_VALIDATION.json).

The separate Lean 4.35 project has its own endpoint and complete local-source audit. It reuses the proved upstream inputs identified in the companion; a separate project does not imply mathematical independence. The final validation uses trace-checked caches for unchanged dependencies.

## Evidence and licenses

[Public validation evidence](02_validation/PUBLIC/README.md) and [supplementary exact-arithmetic checks](03_reproducibility/README.md) state their scope and bind the saved outputs. Written materials use [CC BY-NC 4.0](LICENSE); author-owned Lean/software uses Apache 2.0, with [full license](05_formalization/source/lean435/LICENSE), [notice](05_formalization/source/lean435/NOTICE) and [per-file ownership manifest](05_formalization/source/lean435/OWNERSHIP_AND_LICENSE.json). External dependencies retain their licenses.

The source Paper IV is available in [the versioned Zenodo deposit](https://doi.org/10.5281/zenodo.23089131).
