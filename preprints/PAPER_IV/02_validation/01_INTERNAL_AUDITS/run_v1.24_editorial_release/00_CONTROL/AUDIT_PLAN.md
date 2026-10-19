# Internal editorial audit — Paper IV v1.24

Date: 19 October 2026. Author: Juan Pablo Traverso Gianini.
Execution and editorial review: OpenAI Codex, AI-assisted internal review.

Baseline: `ef31294ad67dfe3f44bc47cec4791c836f55e8aa`. Compare the new article with published v1.23 and the accompanying formal document with the material relocated from it. The author authorized publication after passing this review and prohibited a Lean/Lake rebuild. The audit is not independent human peer review or a new mathematical/kernel audit.

Protected: hypotheses, conclusions, constants, equation labels, proof dependencies, attribution, all frozen Lean files, source archives and earlier audit records. Allowed: exposition, relocation of formal details, typography, navigation and edition metadata. The expanded display in F.5 transcribes an existing premise; its source is identified in the evidence.

E0 baseline and scope; E1 protected mathematical content; E2 bilingual consistency; E3 citations and AI attribution; E4 frozen source identity and historical logs; E5 final TeX/PDF and visual review; E6 README scope and historical navigation; E7 artifact links, privacy and hashes; E8 publication consistency. These are editorial gates, not a repetition of the earlier mathematical E0–E8 certification.

Reproduction: `audit_release.py EDITION V123_MANUSCRIPTS APPROVED_LOCAL FREEZE OUTPUT` reads only documents, frozen source and historical logs. It requires PyMuPDF. It never starts Lean/Lake. Compile only the supplied final TeX for documentary reproduction. Use `verify_editorial.py` for installed release hashes and links.
