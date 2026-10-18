# Formalization companion to exact chordal stability

**Juan Pablo Traverso Gianini**  
Preprint 1.0, 18 October 2026. Formal application of Papers IV and VI. This companion identifies the final source package, its public statement and its trusted boundary. The note develops the stated stability consequence of the source papers; it does not claim a new solution of Erdős Problem 81.

## Public statement and scope

The public endpoint is `ChordalStabilityNote.eventual_root_stability`. It states that there is an order threshold N such that every graph G on Fin n, with n at least N, satisfying chordality, `cp G <= Mval n`, and `2000 * (Mval n - cp G) <= n`, satisfies `RootStability` for the actual degree-defined set `{v | n < 2 * G.degree v}`.

The explicit upper bound `cp G <= Mval n` makes natural subtraction agree with the nonnegative deficit in the manuscript. No structural witness, local modification bound, exact partition formula, or root is assumed in this endpoint. These are obtained in its proof. The threshold is the maximum of the uniform-rounding threshold and `2 * 10^13`; the numerical term does not replace the unknown rounding threshold.

`RootStability` is a record of conclusions. It includes:

| Field | Mathematical conclusion |
|---|---|
| `isClique` | The degree-defined root is a clique |
| `exactFormula` | `cp = B(n,p) - A - 2m` over integers |
| `four` | `cp = cpLe 4` |
| `deficitFormula` | `M-cp = (M-B)+A+2m` |
| `editIdentity` | The edit distance to the complete split reference equals `A+m` |
| `editBound` | That edit distance is at most `M-cp` |
| `square` | `(6p-2n-1)^2 <= 24(M-cp)+25` |
| `canonical` | The root is exactly the set determined by the degree test |

The integer formula for B avoids truncated subtraction. The squared inequality is expressed over rationals. These choices preserve the manuscript's arithmetic meaning.

## Physical adapters and proof dependencies

`PartitionAdapter` converts the actual IV exact partition and the completion of its physical packing into the VI definition of clique partition. It identifies the literal exterior edges, core edges and missing spokes with VI's counting functions. A clique root has `Cdef = 0`. These identifications are proved, not introduced as interface axioms.

`WindowArithmetic` and `GraphWindow` establish the scalar entry bounds, the comparison between maximum modification degree and total edit distance, and recognition of the core by degree. `PaidRootAssembly` then consumes a physical partition and its paid ledger to invoke the actual parametric theorem `PaperVI.cp_window_K4` with parameter four. This intermediate theorem has a paid-root hypothesis, whereas the public endpoint does not.

`NearAssembly` applies this intermediate result to `W.regularized.root` from IV's `NearStructureWitness`. That distinction is essential: the physical accounts belong to the regularized root, rather than to an unrelated field named core. `FarGap` rules out the far regime by comparing an actual rounded packing's completed partition with the actual optimum `cp G`. `GlobalAssembly` supplies the certified fractional optimum, invokes uniform rounding, obtains the near witness by localization, and assembles the conclusion.

The selected proof chain requires IV's `uniformTransferAt`, `NearH1Localization.exists_nearStructureWitness_of_nearRegime`, its localization-by-descent dependency, the physical adapters, and VI's parametric exact construction. It excludes `PaperIV.Erdos81Unconditional`. The application retains its mathematical dependence on IV and VI while having its own source project and endpoint. It does not use Paper V's transfer theorem or VI's additional recourse results. The 18-module VI input cone is the frozen parametric source cut used for this proof; the principal note cites the current editorial manuscript without claiming that its additional modules entered this parametric source cone.

## Final validation and source package

The project uses `leanprover/lean4:v4.35.0` with Mathlib pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its source closure has 343 modules: eight modules of this note, 317 from the IV source cone, and 18 from VI's parametric construction. The inherited IV modules retain their source text and are credited in `AUTHORSHIP_NOTICE.md`. The note’s own modules and gates carry Apache-2.0 copyright headers; the complete license and attribution notice are `lean435/LICENSE` and `lean435/NOTICE`. The note's own modules and gates identify Juan Pablo Traverso Gianini as author. The VI modules are synchronized with the author-credited source version recorded in the manifest; existing third-party credits remain unchanged.

The canonical root build checks `ChordalStabilityNote`. It reuses complete cached artifacts for unchanged dependencies, validates their traces and recompiles changed sources. The source archive itself is portable and contains no caches or local development junctions. This is not a claim that all upstream modules or Mathlib were freshly rebuilt.

The full audit first verifies that every module in the source manifest is present in the imported Lean environment; a missing module causes rejection.

The selected root audit follows 7,125 declaration dependencies, requires the structural and rounding inputs of IV and the parametric theorem of VI, and excludes `PaperIV.Erdos81Unconditional`. The full local-project audit covers 7,393 declarations and visits 10,976 dependencies. Both permit only `propext`, `Classical.choice` and `Quot.sound`; no additional mathematical axiom or `sorryAx` is accepted. `evidence/BUILD_CHECKS.json` records the final commands and exits. `FINAL_FORMAL_VALIDATION.json` binds them to the source and public-entry-point checks.

The immutable archive is `NOTE_II_LEAN435_FINAL_SOURCE_v1.0.zip`. Its SHA-256 is:

```text
b24c5543d719779568ee9c099d453c170d4c69cbd4a31b293f4ee8375e287531
```

`SOURCE_MANIFEST.json` records all source and configuration hashes. Its SHA-256 is:

```text
8bcdf425cee099e6e157dffa4356bb720e6fcd47ec138a2d4bac10b710587f75
```

`lean435/OWNERSHIP_AND_LICENSE.json` enumerates, with hashes, all author-owned Lean sources, including the reused series cuts, released by the author under Apache 2.0. The new full headers cover this note’s specific modules and audit entry points; inherited headers and mathematical attributions are preserved. External dependencies retain their own licenses.

## Reproduction

Extract the archive and run:

```text
cd lean435
lake exe cache get
lake build ChordalStabilityNote
lake env lean -j 1 -s 32768 Endpoint435Gate.lean
lake env lean -j 1 -s 32768 FreezeFullAudit.lean
```

Preserve the supplied `lake-manifest.json`; the cache command retrieves artifacts for the pinned dependencies without requesting a new dependency selection.

The root build executes the selected dependency and axiom audit. The last command audits the complete imported local declaration set. The vendored dependencies are included, so a checkout of the principal papers is not required.

The endpoint retains `cp G <= Mval n` explicitly. Without this hypothesis, natural subtraction could turn a negative mathematical deficit into zero. In the manuscript this is the lower bound on the deficit. The upper bound is `2000 * (Mval n - cp G) <= n`; integer division does not weaken the window. Paper IV supplies the eventual upper bound separately. Combining its threshold with this note's threshold gives the corresponding written corollary for sufficiently large chordal graphs in the stated window; the frozen endpoint keeps the explicit nonnegative-deficit hypothesis.

## Manuscript correspondence and scope

The formal argument uses actual objects throughout. A completed far packing is compared with the actual optimum. The near witness supplies one regularized root with its physical packing and accounts. The adapters identify those counts with VI's functions. The paid-root theorem proves the entry window and applies the exact local construction. Every field of `RootStability` is a conclusion, and the degree test identifies the same root at the end.

The Markdown sources `CHORDAL_STABILITY_NOTE_v1.0_en.md` and `CHORDAL_STABILITY_NOTE_v1.0_es.md` preserve the theorem, constants and displayed equations of the established derivation. The current companion describes only the final validated source package. No inverse transfer theorem, sharper threshold, new exceptional-vertex extension or counting asymptotic is asserted.

## Assistance and responsibility

The principal note retains Paper IV's attribution of Claude, by Anthropic, ChatGPT/Codex, by OpenAI, Aristotle, by Harmonic, Certo and Jacobian for the inherited work. Aristotle's contribution to that work included exploration, counterexample search, proof development, formalization and review, and was not limited to translating finished proofs. For this note, ChatGPT/Codex assisted with the argument, formal interfaces, validation and presentation; Aristotle contributed a separate formalization proposal. Exact-arithmetic regressions supplement the source checks. Computations were reviewed within their stated scope; a finite search does not replace a universal proof. Bibliographic priority and external review are separate matters.

The author remains responsible for the arguments, citations, code, and presentation. No AI system is listed as an author.
