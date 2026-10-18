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
Paper VI research round — general tools.

* Signed edge duals: if an integer edge weight `w` gives total weight at most one to every
  clique, then every (fractional) clique partition costs at least `Σ_{e ∈ E(G)} w e`.
* A variant of the Häggkvist–Janssen completion colouring whose colours are taken from a
  prescribed set `Col` of exterior vertices (used to exclude a special exterior vertex).
-/
module

public import PaperVI.Fractional
public import PaperVI.ListColoring

@[expose] public section

namespace PaperVI

namespace Research

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weight of a vertex set `Q` under an edge weight `w`: the sum of `w` over the edges of
`G` with both ends in `Q`. -/
def setWeight (G : SimpleGraph V) [Fintype G.edgeSet] (w : Sym2 V → ℤ) (Q : Finset V) : ℤ :=
  ∑ e ∈ innerEdges G Q, w e

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge weight summed over a fractional partition: `Σ_Q x_Q w(Q) = Σ_e w e`. -/
theorem sum_mul_setWeight {x : Finset V → ℝ} (hx : IsFracPartition G x) (w : Sym2 V → ℤ) :
    ∑ Q, x Q * (setWeight G w Q : ℝ) = ∑ e ∈ G.edgeFinset, (w e : ℝ) := by
  have h1 : ∀ e ∈ G.edgeFinset, ∑ Q, (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) = 1 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hadj : G.Adj u v := by simpa using he
      rw [← hx.edge u v hadj, ← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext Q
      simp only [mem_filter, mem_univ, true_and, Sym2.mem_toFinset, Sym2.mem_iff]
      constructor
      · intro h; exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
      · rintro ⟨hu, hv⟩ w (rfl | rfl) <;> assumption
  calc ∑ Q, x Q * (setWeight G w Q : ℝ)
      = ∑ Q, ∑ e ∈ G.edgeFinset, (w e : ℝ) * (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) := by
        refine sum_congr rfl fun Q _ => ?_
        unfold setWeight innerEdges
        rw [Int.cast_sum, mul_sum, sum_filter]
        refine sum_congr rfl fun e _ => ?_
        split_ifs <;> simp [mul_comm]
    _ = ∑ e ∈ G.edgeFinset, ∑ Q, (w e : ℝ) * (if ∀ v ∈ e.toFinset, v ∈ Q then x Q else 0) :=
        sum_comm
    _ = ∑ e ∈ G.edgeFinset, (w e : ℝ) := by
        refine sum_congr rfl fun e he => ?_
        rw [← mul_sum, h1 e he, mul_one]

/-- **Signed dual bound (fractional).** If every vertex set in the support of a fractional
clique partition has weight at most one, its cost is at least `Σ_{e ∈ E(G)} w e`. -/
theorem frac_dual_bound {x : Finset V → ℝ} (hx : IsFracPartition G x) (w : Sym2 V → ℤ)
    (hw : ∀ Q, x Q ≠ 0 → setWeight G w Q ≤ 1) :
    ((∑ e ∈ G.edgeFinset, w e : ℤ) : ℝ) ≤ fracValue x := by
  rw [Int.cast_sum, ← sum_mul_setWeight G hx w]
  unfold fracValue
  refine sum_le_sum fun Q _ => ?_
  by_cases hQ : x Q = 0
  · simp [hQ]
  · have h1 : (setWeight G w Q : ℝ) ≤ 1 := by exact_mod_cast hw Q hQ
    have h0 := hx.nonneg Q
    nlinarith

/-- **Signed dual bound (integral).** If every block of a clique partition has weight at most
one, the partition has at least `Σ_{e ∈ E(G)} w e` blocks. -/
theorem dual_bound {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (w : Sym2 V → ℤ)
    (hw : ∀ Q ∈ Bs, setWeight G w Q ≤ 1) :
    ∑ e ∈ G.edgeFinset, w e ≤ Bs.card := by
  obtain ⟨hfrac, hval⟩ := isFracPartition_indicator G hBs
  have := frac_dual_bound G hfrac w (fun Q hQ => by
    have : Q ∈ Bs := by by_contra h; simp [h] at hQ
    exact hw Q this)
  rw [hval] at this
  exact_mod_cast this

/-- **Signed dual bound for `cp`.** If every clique of `G` has weight at most one, then
`cp(G) ≥ Σ_{e ∈ E(G)} w e`. -/
theorem dual_bound_cp (w : Sym2 V → ℤ)
    (hw : ∀ Q : Finset V, G.IsClique (Q : Set V) → setWeight G w Q ≤ 1) :
    ∑ e ∈ G.edgeFinset, w e ≤ cp G := by
  obtain ⟨Bs, hBs, hc⟩ := exists_cp G
  rw [← hc]
  exact dual_bound G hBs w (fun Q hQ => hw Q (hBs.isClique Q hQ))

/-- **Signed dual bound for `cp_{≤ r}`.** If every clique of `G` of order at most `r` has weight
at most one, then `cp_{≤ r}(G) ≥ Σ_{e ∈ E(G)} w e`. -/
theorem dual_bound_cpLe {r : ℕ} (hr : 2 ≤ r) (w : Sym2 V → ℤ)
    (hw : ∀ Q : Finset V, G.IsClique (Q : Set V) → Q.card ≤ r → setWeight G w Q ≤ 1) :
    ∑ e ∈ G.edgeFinset, w e ≤ cpLe r G := by
  obtain ⟨Bs, hBs, hle, hc⟩ := exists_cpLe G hr
  rw [← hc]
  exact dual_bound G hBs w (fun Q hQ => hw Q (hBs.isClique Q hQ) (hle Q hQ))

omit [DecidableRel G.Adj] in
/-- **Completion colouring with prescribed colours.** As `exists_completion_coloring`, but the
colours (exterior vertices) are taken from a prescribed set `Col ⊆ Pᶜ`. If every core vertex
has at most `t` unavailable colours in `Col` and `p + 2t ≤ |Col|`, then there is a symmetric,
proper choice `f a b ∈ Col` of a colour available at both ends of every core pair. -/
theorem exists_completion_coloring_in (P Col : Finset V) (hCol : Col ⊆ Pᶜ)
    (avail : V → V → Prop) [DecidableRel avail]
    (t : ℕ) (hF : ∀ a ∈ P, (Col.filter (fun x => ¬ avail a x)).card ≤ t)
    (hq : P.card + 2 * t ≤ Col.card) :
    ∃ f : V → V → V, (∀ a ∈ P, ∀ b ∈ P, a ≠ b → f a b = f b a) ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → f a b ∈ Col ∧ f a b ∉ P ∧ avail a (f a b) ∧
        avail b (f a b)) ∧
      (∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → f a b ≠ f a b') := by
  classical
  let lists : (⊤ : SimpleGraph P).edgeSet → Finset V := fun e =>
    Col.filter (fun x => ∀ a ∈ (e : Sym2 P).toFinset, avail a.1 x)
  have hLists : ∀ e, Fintype.card P ≤ (lists e).card := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [Fintype.card_coe]
      have hsub : Col \ (Col.filter (fun x => ¬ avail a.1 x) ∪ Col.filter (fun x => ¬ avail b.1 x))
          ⊆ lists ⟨s(a, b), he⟩ := by
        intro x hx
        simp only [mem_sdiff, mem_union, mem_filter, not_or, not_and, not_not] at hx
        simp only [lists, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff]
        refine ⟨hx.1, ?_⟩
        rintro c (rfl | rfl)
        · exact hx.2.1 hx.1
        · exact hx.2.2 hx.1
      have h1 := card_le_card hsub
      have h2 := le_card_sdiff (Col.filter (fun x => ¬ avail a.1 x) ∪
        Col.filter (fun x => ¬ avail b.1 x)) Col
      have h3 := card_union_le (Col.filter (fun x => ¬ avail a.1 x))
        (Col.filter (fun x => ¬ avail b.1 x))
      have h4 := hF a.1 a.2
      have h5 := hF b.1 b.2
      omega
  obtain ⟨col, hcol⟩ := HaggkvistJanssen.exists_listEdgeColoring_complete lists hLists
  have hedge : ∀ a b : V, ∀ h : a ∈ P ∧ b ∈ P ∧ a ≠ b,
      s((⟨a, h.1⟩ : P), ⟨b, h.2.1⟩) ∈ (⊤ : SimpleGraph P).edgeSet := by
    intro a b h
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    exact fun h' => h.2.2 (congrArg Subtype.val h')
  let f : V → V → V := fun a b =>
    if h : a ∈ P ∧ b ∈ P ∧ a ≠ b then col ⟨s(⟨a, h.1⟩, ⟨b, h.2.1⟩), hedge a b h⟩ else a
  have hf : ∀ a b (h : a ∈ P ∧ b ∈ P ∧ a ≠ b), f a b = col ⟨s(⟨a, h.1⟩, ⟨b, h.2.1⟩), hedge a b h⟩ :=
    fun a b h => by simp only [f, dif_pos h]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [hf a b ⟨ha, hb, hab⟩, hf b a ⟨hb, ha, hab.symm⟩]
    congr 1
    exact Subtype.ext Sym2.eq_swap
  · intro a ha b hb hab
    rw [hf a b ⟨ha, hb, hab⟩]
    have := hcol ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hedge a b ⟨ha, hb, hab⟩⟩
    simp only [lists, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff] at this
    exact ⟨this.1, mem_compl.mp (hCol this.1), this.2 _ (Or.inl rfl), this.2 _ (Or.inr rfl)⟩
  · intro a ha b hb b' hb' hab hab' hbb'
    rw [hf a b ⟨ha, hb, hab⟩, hf a b' ⟨ha, hb', hab'⟩]
    apply col.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, ⟨a, ha⟩, by simp, by simp⟩
    intro h
    have := congrArg Subtype.val h
    simp only [Sym2.congr_right, Subtype.mk.injEq] at this
    exact hbb' this

end Research

end PaperVI
