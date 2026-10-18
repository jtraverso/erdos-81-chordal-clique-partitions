# Paper V — Preprint 1.0: Lean sources

The canonical public entry point is `PaperV.lean`. The supplied `lean-toolchain` and `lake-manifest.json` fix Lean 4.35 and the exact dependency revisions. Do not run `lake update` when reproducing this snapshot. With the pinned Lean toolchain installed, obtain the pinned dependencies and their cache with `lake exe cache get`, then run:

```text
lake build PaperV
lake env lean PaperVManuscriptGate.lean
lake env lean PaperVSupplementGate.lean
lake env lean PaperVImprovementsGate.lean
lake env lean PaperVReleaseGate.lean
lake env lean FreezeFullAudit.lean
```

The remaining standalone gates are listed in the separate `CHECKED_PUBLICATION_GATES_435.json` distributed with the formal companion. The source manifest in this archive hashes every source/configuration/license file. The separate validation record contains exact commands, exit receipts, public-module coverage, statement types, axiom footprints and the final full declaration audit. No compiled artifacts or workstation-specific dependency paths are required by this archive.

The new `PaperV.CopyPackings` interface constructs the actual image multiset of specified copied packings, rather than replacing them with an unrelated existential witness. Other mathematical source bodies are preserved from the checked baseline; copyright headers and public validation interfaces are updated for this release. Source proof validity is checked by the fresh build and axiom records, not inferred from a historical label.

Author contributions: copyright 2026 Juan Pablo Traverso Gianini, Apache License 2.0. Existing mathematical attributions and third-party notices are retained. Written documentation follows CC BY-NC 4.0. See LICENSES/NOTICE.md for the precise distinction. Kernel checking does not certify the executable SEAL implementation end to end, external human review or historical priority.
