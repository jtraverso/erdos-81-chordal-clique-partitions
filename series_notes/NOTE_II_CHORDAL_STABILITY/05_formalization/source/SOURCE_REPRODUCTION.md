# Final source project: research note II

Author: Juan Pablo Traverso Gianini. Extract this archive, enter `lean435`, and preserve the supplied `lake-manifest.json`, then run `lake exe cache get`, `lake build ChordalStabilityNote`, `lake env lean -j 1 -s 32768 Endpoint435Gate.lean`, and `lake env lean -j 1 -s 32768 FreezeFullAudit.lean`. Pinned Mathlib sources are fetched by Lake; use its cache setup as appropriate. All required local sources are included. No development cache or junction is packaged.

The source manifest is authoritative. The full audit verifies that every listed module is imported, then inspects all local declarations and their external axiom footprints. Only propext, Classical.choice and Quot.sound are allowed. The selected root audit checks the actual upstream inputs and excludes IV’s final global-bound theorem. This is dependency validation, not mathematical independence from IV.

Author-owned Lean sources, including the reused series cuts enumerated in lean435/OWNERSHIP_AND_LICENSE.json, are released under Apache License 2.0. See lean435/LICENSE, lean435/NOTICE and AUTHORSHIP_NOTICE.md. External dependencies and preserved third-party notices retain their own terms.
