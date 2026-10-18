/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — the local bounds (3) that follow from `h = Δ(G △ S)`, and the arithmetic (1)
of the parameters `p = ⌊(n+1)/3⌋`, `q = n - p`.
-/
module

public import PaperVI.Counting

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Arithmetic of `p, q, M(n)` -/

theorem p_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (n + 1) / 3 := by omega

theorem q_le_two_p_add_one (n : ℕ) : n - (n + 1) / 3 ≤ 2 * ((n + 1) / 3) + 1 := by omega

theorem two_p_le_q_add_one (n : ℕ) : 2 * ((n + 1) / 3) ≤ n - (n + 1) / 3 + 1 := by omega

theorem p_le_q (n : ℕ) : (n + 1) / 3 ≤ n - (n + 1) / 3 := by omega

theorem choose_two_nat (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  have h := two_mul_choose_two k
  have : (2 * k.choose 2 + k : ℕ) = ((k * k : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this

/-- Identity (1): `pq - binom(p,2) = M(n)`. -/
theorem Mval_eq (n : ℕ) :
    (Mval n : ℤ) = ((n + 1) / 3 : ℕ) * ((n - (n + 1) / 3 : ℕ) : ℤ) -
      (((n + 1) / 3).choose 2 : ℤ) := by
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 :=
    ⟨n / 3, by omega⟩
  · have hq : n - (n + 1) / 3 = 2 * k := by omega
    have hp : (n + 1) / 3 = k := by omega
    have hN : n * (n + 1) = 9 * (k * k) + 3 * k := by subst hk; ring
    have hc := choose_two_nat k
    rw [hq, hp, Mval, hN, show (k:ℤ) * ((2 * k : ℕ) : ℤ) = 2 * ((k * k : ℕ) : ℤ) by
      push_cast; ring]
    generalize k * k = K at hc ⊢
    omega
  · have hq : n - (n + 1) / 3 = 2 * k + 1 := by omega
    have hp : (n + 1) / 3 = k := by omega
    have hN : n * (n + 1) = 9 * (k * k) + 9 * k + 2 := by subst hk; ring
    have hc := choose_two_nat k
    rw [hq, hp, Mval, hN, show (k:ℤ) * ((2 * k + 1 : ℕ) : ℤ) = 2 * ((k * k : ℕ) : ℤ) + k by
      push_cast; ring]
    generalize k * k = K at hc ⊢
    omega
  · have hq : n - (n + 1) / 3 = 2 * k + 1 := by omega
    have hp : (n + 1) / 3 = k + 1 := by omega
    have hN : n * (n + 1) = 9 * (k * k) + 15 * k + 6 := by subst hk; ring
    have hc := choose_two_nat (k + 1)
    rw [show (k + 1) * (k + 1) = k * k + 2 * k + 1 by ring] at hc
    rw [hq, hp, Mval, hN, show ((k + 1 : ℕ) : ℤ) * ((2 * k + 1 : ℕ) : ℤ) =
      2 * ((k * k : ℕ) : ℤ) + 3 * k + 1 by push_cast; ring]
    generalize k * k = K at hc ⊢
    omega

/-! ### Adjacency in `G △ S` -/

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem editGraph_adj (u v : V) :
    (editGraph G P).Adj u v ↔
      (G.Adj u v ∧ ¬ (u ≠ v ∧ (u ∈ P ∨ v ∈ P))) ∨ ((u ≠ v ∧ (u ∈ P ∨ v ∈ P)) ∧ ¬ G.Adj u v) := by
  simp [editGraph, symmDiff_def, refGraph]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Any set of neighbours in `G △ S` has at most `h` elements. -/
theorem card_le_editDegree (v : V) (s : Finset V) (hs : ∀ w ∈ s, (editGraph G P).Adj v w) :
    s.card ≤ editDegree G P := by
  classical
  unfold editDegree
  calc s.card ≤ ((editGraph G P).neighborFinset v).card :=
        card_le_card (fun w hw => by simpa using hs w hw)
    _ = (editGraph G P).degree v := (SimpleGraph.card_neighborFinset_eq_degree _ _)
    _ ≤ _ := by convert (editGraph G P).degree_le_maxDegree v

/-- (3), exterior vertices: `β_x + d_H(x) ≤ h`. -/
theorem ext_local_bound (x : V) (hx : x ∉ P) :
    (P.filter (fun a => ¬ G.Adj x a)).card + (Pᶜ.filter (fun y => G.Adj x y)).card
      ≤ editDegree G P := by
  rw [← card_union_of_disjoint]
  · apply card_le_editDegree
    intro w hw
    rw [editGraph_adj]
    simp only [mem_union, mem_filter, mem_compl] at hw
    rcases hw with ⟨hw, hadj⟩ | ⟨hw, hadj⟩
    · right; exact ⟨⟨fun h => hx (by rw [h]; exact hw), Or.inr hw⟩, hadj⟩
    · left; exact ⟨hadj, fun h => h.2.elim hx hw⟩
  · rw [disjoint_left]
    intro w h1 h2
    simp only [mem_filter, mem_compl] at h1 h2
    exact h2.1 h1.1

/-- (3), core vertices: `c_a + α_a ≤ h`. -/
theorem core_local_bound (a : V) (ha : a ∈ P) :
    (P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b)).card + (Pᶜ.filter (fun x => ¬ G.Adj a x)).card
      ≤ editDegree G P := by
  rw [← card_union_of_disjoint]
  · apply card_le_editDegree
    intro w hw
    rw [editGraph_adj]
    simp only [mem_union, mem_filter, mem_compl] at hw
    rcases hw with ⟨hw, hne, hadj⟩ | ⟨hw, hadj⟩
    · right; exact ⟨⟨hne.symm, Or.inl ha⟩, hadj⟩
    · right; exact ⟨⟨fun h => hw (h ▸ ha), Or.inl ha⟩, hadj⟩
  · rw [disjoint_left]
    intro w h1 h2
    simp only [mem_filter, mem_compl] at h1 h2
    exact h2.1 h1.1

/-! ### Exterior edges -/

theorem mem_extEdges {x y : V} : s(x, y) ∈ extEdges G P ↔ G.Adj x y ∧ x ∉ P ∧ y ∉ P := by
  classical
  simp only [extEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq]

theorem mem_coreEdges {x y : V} : s(x, y) ∈ coreEdges G P ↔ G.Adj x y ∧ x ∈ P ∧ y ∈ P := by
  classical
  simp only [coreEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Sym2.mem_toFinset, Sym2.mem_iff, forall_eq_or_imp, forall_eq]

theorem card_extEdges_incident_le (x : V) :
    ((extEdges G P).filter (fun e => x ∈ e)).card ≤ (Pᶜ.filter (fun y => G.Adj x y)).card := by
  classical
  refine le_trans (card_le_card ?_) (card_image_le (f := fun y => s(x, y)))
  intro e he
  simp only [mem_filter] at he
  obtain ⟨he, hxe⟩ := he
  obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
  rw [mem_extEdges] at he
  simp only [mem_image, mem_filter, mem_compl]
  exact ⟨y, ⟨he.2.2, he.1⟩, rfl⟩

/-- Double counting of incidences. -/
theorem sum_card_filter_comm {α β : Type*} (X : Finset α) (S : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] :
    ∑ x ∈ X, (S.filter (fun e => R x e)).card = ∑ e ∈ S, (X.filter (fun x => R x e)).card := by
  simp only [card_filter]
  exact sum_comm

/-- (3): `2m ≤ qh`. -/
theorem two_mCount_le : 2 * mCount G P ≤ Pᶜ.card * editDegree G P := by
  classical
  have h1 : ∑ x ∈ Pᶜ, ((extEdges G P).filter (fun e => x ∈ e)).card = 2 * mCount G P := by
    rw [sum_card_filter_comm, mCount, card_eq_sum_ones, mul_sum, mul_one]
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_extEdges] at he
      have : Pᶜ.filter (fun z => z ∈ s(x, y)) = {x, y} := by
        ext z
        simp only [mem_filter, mem_compl, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨he.2.1, Or.inl rfl⟩
          · exact ⟨he.2.2, Or.inr rfl⟩
      rw [this, card_pair he.1.ne]
  rw [← h1]
  calc ∑ x ∈ Pᶜ, ((extEdges G P).filter (fun e => x ∈ e)).card
      ≤ ∑ _x ∈ Pᶜ, editDegree G P := by
        refine sum_le_sum fun x hx => ?_
        have hx' : x ∉ P := by simpa using hx
        exact (card_extEdges_incident_le G P x).trans
          (le_trans (Nat.le_add_left _ _) (ext_local_bound G P x hx'))
    _ = _ := by rw [sum_const, smul_eq_mul]

end PaperVI
