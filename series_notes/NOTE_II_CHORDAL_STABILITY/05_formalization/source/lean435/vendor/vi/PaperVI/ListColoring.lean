/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — Section 2.3: completion of the residual core by list edge colouring, using the
Häggkvist–Janssen theorem `χ'_ℓ(K_p) ≤ p` (ported dependency `HaggkvistJanssen`).
-/
module

public import PaperVI.Lifting
public import Solution

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Completion colouring (Section 2.3).** Let `avail a x` say that the crossing edge `ax`
is still available. If every core vertex has at most `t` unavailable exterior vertices and
`p + 2t ≤ q`, then there is a symmetric choice `f a b` of an exterior vertex for every pair of
distinct core vertices, available at both ends, such that pairs sharing a core vertex receive
distinct exterior vertices. This is a proper list edge colouring of the complete graph on `P`
with lists of size at least `p`, obtained from the Häggkvist–Janssen theorem. -/
theorem exists_completion_coloring (P : Finset V) (avail : V → V → Prop) [DecidableRel avail]
    (t : ℕ) (hF : ∀ a ∈ P, (Pᶜ.filter (fun x => ¬ avail a x)).card ≤ t)
    (hq : P.card + 2 * t ≤ Pᶜ.card) :
    ∃ f : V → V → V, (∀ a ∈ P, ∀ b ∈ P, a ≠ b → f a b = f b a) ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → f a b ∉ P ∧ avail a (f a b) ∧ avail b (f a b)) ∧
      (∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → f a b ≠ f a b') := by
  classical
  let lists : (⊤ : SimpleGraph P).edgeSet → Finset V := fun e =>
    Pᶜ.filter (fun x => ∀ a ∈ (e : Sym2 P).toFinset, avail a.1 x)
  have hLists : ∀ e, Fintype.card P ≤ (lists e).card := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | h a b =>
      rw [Fintype.card_coe]
      have hsub : Pᶜ \ (Pᶜ.filter (fun x => ¬ avail a.1 x) ∪ Pᶜ.filter (fun x => ¬ avail b.1 x))
          ⊆ lists ⟨s(a, b), he⟩ := by
        intro x hx
        simp only [mem_sdiff, mem_union, mem_filter, not_or, not_and, not_not] at hx
        simp only [lists, mem_filter, Sym2.mem_toFinset, Sym2.mem_iff]
        refine ⟨hx.1, ?_⟩
        rintro c (rfl | rfl)
        · exact hx.2.1 hx.1
        · exact hx.2.2 hx.1
      have h1 := card_le_card hsub
      have h2 := le_card_sdiff (Pᶜ.filter (fun x => ¬ avail a.1 x) ∪
        Pᶜ.filter (fun x => ¬ avail b.1 x)) Pᶜ
      have h3 := card_union_le (Pᶜ.filter (fun x => ¬ avail a.1 x))
        (Pᶜ.filter (fun x => ¬ avail b.1 x))
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
    simp only [lists, mem_filter, mem_compl, Sym2.mem_toFinset, Sym2.mem_iff] at this
    exact ⟨this.1, this.2 _ (Or.inl rfl), this.2 _ (Or.inr rfl)⟩
  · intro a ha b hb b' hb' hab hab' hbb'
    rw [hf a b ⟨ha, hb, hab⟩, hf a b' ⟨ha, hb', hab'⟩]
    apply col.valid
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, ⟨a, ha⟩, by simp, by simp⟩
    intro h
    have := congrArg Subtype.val h
    simp only [Sym2.congr_right, Subtype.mk.injEq] at this
    exact hbb' this

end PaperVI
