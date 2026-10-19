# Editorial release integrity — Paper IV v1.24

`MANIFEST.json` binds the new documents, navigation and editorial evidence. It is an incremental documentary manifest; it does not replace the old mathematical/formal release manifest. Manifest files, the root aggregate manifest and this manifest's verification receipt are excluded from self-hashing.

`python verify_editorial.py PATH_TO_REPOSITORY` verifies every recorded file without Lean/Lake. The original Lean ZIP and annex remain linked by their historical hashes in the companion and new audit. The aggregate root manifest is updated for changed/new files while retaining entries for unchanged files, including those not materialized in the sparse publication checkout.

The manifest records the released artifact bytes, not a claim of new kernel execution or human peer review. GitHub commit history supplies ordering; the Zenodo receipt records the deposited PDFs separately.
