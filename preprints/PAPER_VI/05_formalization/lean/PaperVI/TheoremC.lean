/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
SPDX-License-Identifier: Apache-2.0

The Apache-2.0 grant applies to the author-written formalization in this file.
Existing mathematical attributions, author credits and provenance below are retained.
-/

/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — Theorem C (restriction to triangles).
-/
module

public import PaperVI.TheoremA

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The root-selection estimate of Section 4, in untruncated form. -/
theorem arith_candidates_C {p q h k bx by_ dx dy sat nD m : ℕ} (hq1 : q ≤ 2 * p + 1)
    (hq2 : p + 18 * h ≤ q) (h1 : p ≤ k + bx + by_ + 1 * dx + 1 * dy + sat)
    (h2 : bx + dx + 1 ≤ h) (h3 : by_ + dy + 1 ≤ h) (h4 : 2 * h * sat ≤ 1 * nD)
    (h5 : nD + 1 ≤ m) (h6 : 2 * m ≤ q * h) : 1 ≤ k := by
  have hh : 1 ≤ h := by omega
  have hs : 4 * sat < q := by
    by_contra hc
    push_neg at hc
    have := Nat.mul_le_mul_right h hc
    nlinarith
  omega

/-- Block types used in Theorem C: `(1,1)`, `(2,1)` and `(1,2)`. -/
def IsTypeC (P B : Finset V) : Prop :=
  (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
    (coreSize P B = 1 ∧ extSize P B = 2)

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The triangle construction of Section 4: each exterior edge gets a core root (load at
most `2h`), and the residual core is completed by Häggkvist–Janssen. -/
theorem exists_partition_C (hq1 : Pᶜ.card ≤ 2 * P.card + 1)
    (hq2 : P.card + 18 * editDegree G P ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs, IsTypeC P B := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_of_lift G P (σ := fun _ => 1) (c := 1)
    (r := 2 * editDegree G P) (need := 1)
    (fun _ _ => le_rfl) (fun _ _ => by omega)
    (fun k bx by_ dx dy sat nD h1 h2 h3 h4 h5 h6 =>
      arith_candidates_C hq1 hq2 h1 h2 h3 h4 h5 h6)
    (by omega)
  refine ⟨Bs, hBs, fun B hB => ?_⟩
  rcases htypes B hB with h | h | ⟨e, -, -, hc, hb⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hc, hb⟩)

/-- **Theorem C (restriction to triangles).** Under the hypothesis of Theorem A
(`p ≥ 18h + 1`), `cp_{≤3}(G) = s - u - m = M(n) + C - A - m`, and hence
`cp_{≤3}(G) - cp(G) = m`. The optimum is attained by an exact partition into crossing edges,
`u` triangles of type `(2,1)` and `m` triangles of type `(1,2)`. -/
theorem theoremC (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    (cpLe 3 G : ℤ) = (sCount G P : ℤ) - uCount G P - mCount G P ∧
    (cpLe 3 G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - mCount G P ∧
    (cpLe 3 G : ℤ) - cp G = mCount G P ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cpLe 3 G ∧
      (∀ B ∈ Bs, IsTypeC P B) ∧ typeCount P Bs 1 2 = mCount G P ∧
      typeCount P Bs 2 1 = uCount G P := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by
    rw [hq, hP]; exact q_le_two_p_add_one _
  have hq2 : P.card + 18 * editDegree G P ≤ Pᶜ.card := by
    have := two_p_le_q_add_one (Fintype.card V)
    rw [hq, hP] at *; omega
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_C G P hq1 hq2
  obtain ⟨cu, cm, cs, ccard⟩ := type_counts G P hBs (fun B hB => by
    rcases htypes B hB with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  have z22 : typeCount P Bs 2 2 = 0 := by
    unfold typeCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro B hB ⟨h1, h2⟩
    rcases htypes B hB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> omega
  have z32 : typeCount P Bs 3 2 = 0 := by
    unfold typeCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro B hB ⟨h1, h2⟩
    rcases htypes B hB with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> omega
  have hle3 : ∀ B ∈ Bs, B.card ≤ 3 := by
    intro B hB
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hlow := cpLe_three_ge G P
  have hup := cpLe_le hBs hle3
  have hC : (cpLe 3 G : ℤ) = (sCount G P : ℤ) - uCount G P - mCount G P := by omega
  have hA := (theoremA G P hn hP hh).2.2.1
  obtain ⟨hAM, -⟩ := theoremA G P hn hP hh
  refine ⟨hC, by linarith, by linarith, Bs, hBs, by omega, htypes, by omega, by omega⟩

end PaperVI
