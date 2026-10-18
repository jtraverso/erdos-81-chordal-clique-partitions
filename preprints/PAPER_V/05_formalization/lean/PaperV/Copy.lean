/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Original mathematical attributions and third-party notices are retained below.
-/

/-
Paper V formalization and integration.
Authors: Juan Pablo Traverso Gianini

Original mathematical attributions and existing source/port provenance are
retained below; this author credit does not reattribute those prior results.
-/

/-
Paper IV/V — §4.1 copy inequalities (umbrella module). The former monolithic `Copy.lean` (2645 lines) was split on
2026-09-14 into `CopyCore` (definitions, Theorem 4.2, edge load), `CopyN1Degree` (subcubic) and `CopyN1K4`
(`K₄`-free, structural theorem). Importing `PaperV.Copy` provides exactly the same declarations as before.
-/
module

public import PaperV.CopyCore
public import PaperV.CopyN1Degree
public import PaperV.CopyN1K4

@[expose] public section
