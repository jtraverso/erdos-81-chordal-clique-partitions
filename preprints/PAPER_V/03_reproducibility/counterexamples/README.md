# Paper V, Section 9: finite counterexamples

Run from this directory with normal Python execution (do not use `-O`):

```text
python bk_completion_certificates.py --verify-only
python replay_saved_and_negative.py
```

This uses only the Python standard library. It reconstructs the unit-capacity BK resource system, checks the complete rational dual of value 19/2, and enumerates all 70 optimal nine-element packings and their residual matching parameter beta=2. Integer weak duality makes 9 an upper bound; the enumerated feasible families attain it. The saved certificate is compared with the recomputed record.

The optional command without `--verify-only` searches for a certificate with SciPy. Numerical search is not required to verify the saved one. `VALIDATION.json` and the logs record the current replay and a deliberately altered dual rejected by the checker. Assertions must remain enabled. This finite check is separate from the universal mathematical proofs and from the kernel-checked finite BK, CLON-2, STAR-T2 and Steiner declarations in the Lean project.

Copyright (c) 2026 Juan Pablo Traverso Gianini. Software: Apache 2.0. The saved mathematical data and written documentation accompany the series under its documented material license.
