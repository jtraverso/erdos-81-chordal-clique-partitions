/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — Section 6: local stability for chordal graphs (Lemma 6.1, formulas (20), (21)).
-/
module

public import PaperVI.TheoremA
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is chordal if it has no induced cycle of length at least four. (An embedding
`cycleGraph n ↪g G` is an induced copy of the `n`-cycle.) -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ n, 4 ≤ n → IsEmpty (SimpleGraph.cycleGraph n ↪g G)

omit [Fintype V] [DecidableEq V] in
/-- An induced 4-cycle `a x b y`. -/
theorem induced_four_cycle (G : SimpleGraph V) {a x b y : V} (h1 : G.Adj a x) (h2 : G.Adj x b)
    (h3 : G.Adj b y) (h4 : G.Adj y a) (h5 : ¬ G.Adj a b) (h6 : ¬ G.Adj x y) (hab : a ≠ b)
    (hxy : x ≠ y) : Nonempty (SimpleGraph.cycleGraph 4 ↪g G) := by
  have hax := h1.ne; have hxb := h2.ne; have hby := h3.ne; have hya := h4.ne
  refine ⟨⟨⟨![a, x, b, y], ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j
    change G.Adj (![a,x,b,y] i) (![a,x,b,y] j) ↔ (SimpleGraph.cycleGraph 4).Adj i j
    rw [SimpleGraph.cycleGraph_adj]
    fin_cases i <;> fin_cases j <;> simp_all [G.adj_comm] <;> decide

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- **Lemma 6.1 (core rigidity).** Under the hypothesis of Theorem A, a chordal graph has a
complete core: every pair of core vertices is adjacent, i.e. `C = 0`. -/
theorem core_complete_of_chordal (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 18 * editDegree G P + 1 ≤ P.card)
    (hG : IsChordal G) : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → G.Adj a b := by
  intro a ha b hb hab
  by_contra hnot
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  -- `h ≥ 1`
  have hh1 : 1 ≤ editDegree G P := by
    have := card_le_editDegree G P a {b} (fun w hw => by
      rw [mem_singleton] at hw; subst hw
      rw [editGraph_adj]; right; exact ⟨⟨hab, Or.inl ha⟩, hnot⟩)
    simpa using this
  -- common exterior neighbours
  set X := Pᶜ.filter (fun x => G.Adj a x ∧ G.Adj b x) with hX
  have hcov : Pᶜ ⊆ X ∪ Pᶜ.filter (fun x => ¬ G.Adj a x) ∪ Pᶜ.filter (fun x => ¬ G.Adj b x) := by
    intro x hx
    by_cases h1 : G.Adj a x
    · by_cases h2 : G.Adj b x
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx, h1, h2⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hx, h2⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx, h1⟩))
  have hXcard : Pᶜ.card ≤ X.card + 2 * editDegree G P := by
    have h1 := card_le_card hcov
    have h2 := card_union_le (X ∪ Pᶜ.filter (fun x => ¬ G.Adj a x))
      (Pᶜ.filter (fun x => ¬ G.Adj b x))
    have h3 := card_union_le X (Pᶜ.filter (fun x => ¬ G.Adj a x))
    have h4 := core_local_bound G P a ha
    have h5 := core_local_bound G P b hb
    omega
  have hXpos : 0 < X.card := by omega
  obtain ⟨x, hxX⟩ := card_pos.mp hXpos
  have hxX' := mem_filter.mp hxX
  have hxP : x ∉ P := by simpa using hxX'.1
  -- a common neighbour `y` of `a, b` not adjacent to `x`
  have hY : 0 < ((X.erase x).filter (fun y => ¬ G.Adj x y)).card := by
    have h1 := card_filter_add_card_filter_not (s := X.erase x) (fun y => G.Adj x y)
    have h2 := card_erase_of_mem hxX
    have h3 : ((X.erase x).filter (fun y => G.Adj x y)).card ≤ editDegree G P := by
      have := ext_local_bound G P x hxP
      refine le_trans (card_le_card ?_) (le_trans (Nat.le_add_left _ _) this)
      intro y hy
      simp only [mem_filter, mem_erase] at hy
      exact mem_filter.mpr ⟨(mem_filter.mp hy.1.2).1, hy.2⟩
    omega
  obtain ⟨y, hy⟩ := card_pos.mp hY
  simp only [mem_filter, mem_erase] at hy
  obtain ⟨⟨hyx, hyX⟩, hxy⟩ := hy
  have hyX' := mem_filter.mp hyX
  obtain ⟨e⟩ := induced_four_cycle G hxX'.2.1 hxX'.2.2.symm hyX'.2.2 hyX'.2.1.symm hnot hxy hab
    (Ne.symm hyx)
  exact (hG 4 le_rfl).false e

/-- Formula (20): for chordal graphs in the neighbourhood of Theorem A,
`cp(G) = M(n) - A - 2m`. -/
theorem cp_chordal (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) (hG : IsChordal G) :
    Cdef G P = 0 ∧ (cp G : ℤ) = Mval (Fintype.card V) - Adef G P - 2 * mCount G P := by
  have hcore := core_complete_of_chordal G P hn hP hh hG
  have hC : Cdef G P = 0 := by
    unfold Cdef uCount
    have : coreEdges G P = innerEdges G P := rfl
    rw [this, card_innerEdges_of_isClique G P (fun a ha b hb hab => hcore a ha b hb hab)]
    ring
  refine ⟨hC, ?_⟩
  have := (theoremA G P hn hP hh).1
  rw [this, hC]; ring

/-! ### The labelled edit distance -/

instance : DecidableRel (editGraph G P).Adj := fun u v =>
  decidable_of_iff _ (editGraph_adj G P u v).symm

/-- The labelled edit distance `d_edit = |E(G) △ E(S)| = |E(G △ S)|`. -/
def editDistance : ℕ := (editGraph G P).edgeFinset.card

theorem card_crossEdges_top :
    sCount (⊤ : SimpleGraph V) P = P.card * (Fintype.card V - P.card) := by
  have h := card_insideFilter_cross (⊤ : SimpleGraph V) P univ
    (fun _ _ _ _ h => (SimpleGraph.top_adj _ _).mpr h)
  have e : insideFilter (crossEdges (⊤ : SimpleGraph V) P) univ = crossEdges ⊤ P := by
    ext e; simp only [insideFilter, mem_filter, mem_univ, implies_true, and_true]
  rw [e] at h
  unfold sCount; rw [h]
  unfold coreSize extSize
  rw [univ_inter, ← compl_eq_univ_sdiff, card_compl]

theorem card_coreEdges_top : uCount (⊤ : SimpleGraph V) P = P.card.choose 2 := by
  have h := card_insideFilter_core (⊤ : SimpleGraph V) P univ
    (fun _ _ _ _ h => (SimpleGraph.top_adj _ _).mpr h)
  have e : insideFilter (coreEdges (⊤ : SimpleGraph V) P) univ = coreEdges ⊤ P := by
    ext e; simp only [insideFilter, mem_filter, mem_univ, implies_true, and_true]
  rw [e] at h
  unfold uCount; rw [h]
  unfold coreSize
  rw [univ_inter]

theorem mem_crossEdges (H : SimpleGraph V) [DecidableRel H.Adj] {x y : V} :
    s(x, y) ∈ crossEdges H P ↔ H.Adj x y ∧ ((x ∈ P ∧ y ∉ P) ∨ (x ∉ P ∧ y ∈ P)) := by
  simp only [crossEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    Sym2.mem_toFinset, Sym2.mem_iff, exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨h, by tauto⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by tauto⟩

/-- `d_edit = C + A + m`. -/
theorem editDistance_eq :
    (editDistance G P : ℤ) = Cdef G P + Adef G P + mCount G P := by
  -- decomposition of the edges of `G △ S` by kind
  have hk : (coreEdges (editGraph G P) P).card + (extEdges (editGraph G P) P).card +
      (crossEdges (editGraph G P) P).card = (editGraph G P).edgeFinset.card :=
    card_kinds P (editGraph G P).edgeFinset
  have hcore : (coreEdges (⊤ : SimpleGraph V) P).card =
      (coreEdges G P).card + (coreEdges (editGraph G P) P).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext e
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_union, mem_coreEdges, mem_coreEdges, mem_coreEdges, SimpleGraph.top_adj,
          editGraph_adj]
        by_cases hxy : x = y
        · subst hxy; simp
        · tauto
    · rw [disjoint_left]; intro e h1 h2
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_coreEdges] at h1
        rw [mem_coreEdges, editGraph_adj] at h2
        have := h1.1.ne
        tauto
  have hcross : (crossEdges (⊤ : SimpleGraph V) P).card =
      (crossEdges G P).card + (crossEdges (editGraph G P) P).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext e
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_union, mem_crossEdges, mem_crossEdges, mem_crossEdges, SimpleGraph.top_adj,
          editGraph_adj]
        by_cases hxy : x = y
        · subst hxy; simp
        · tauto
    · rw [disjoint_left]; intro e h1 h2
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_crossEdges] at h1
        rw [mem_crossEdges, editGraph_adj] at h2
        have := h1.1.ne
        tauto
  have hext : extEdges (editGraph G P) P = extEdges G P := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_extEdges, mem_extEdges, editGraph_adj]
      tauto
  have hc1 := card_coreEdges_top (V := V) P
  have hc2 := card_crossEdges_top (V := V) P
  unfold uCount at hc1
  unfold sCount at hc2
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  unfold editDistance Cdef Adef uCount sCount mCount
  rw [← hk, hext]
  push_cast [hpn]
  have : ((P.card * (Fintype.card V - P.card) : ℕ) : ℤ) =
      (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) := by push_cast [hpn]; ring
  omega

/-- Formula (21) and the local equality case: for chordal graphs in the neighbourhood of
Theorem A, `d_edit = A + m` and `d_edit ≤ M(n) - cp(G) ≤ 2 d_edit`; moreover
`cp(G) = M(n)` forces `G = S`. -/
theorem chordal_stability (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) (hG : IsChordal G) :
    (editDistance G P : ℤ) = Adef G P + mCount G P ∧
    (editDistance G P : ℤ) ≤ Mval (Fintype.card V) - cp G ∧
    (Mval (Fintype.card V) : ℤ) - cp G ≤ 2 * editDistance G P ∧
    (cp G = Mval (Fintype.card V) → G = refGraph P) := by
  obtain ⟨hC, hcp⟩ := cp_chordal G P hn hP hh hG
  have hd := editDistance_eq G P
  rw [hC, zero_add] at hd
  -- `A ≥ 0`
  have hA : 0 ≤ Adef G P := by
    have hsub : crossEdges G P ⊆ crossEdges (⊤ : SimpleGraph V) P := by
      intro e he
      induction e using Sym2.ind with
      | h x y =>
        rw [mem_crossEdges] at he ⊢
        exact ⟨he.1.ne, he.2⟩
    have h1 := card_le_card hsub
    have h2 := card_crossEdges_top (V := V) P
    unfold sCount at h2
    have hpn : P.card ≤ Fintype.card V := card_le_univ P
    unfold Adef sCount
    rw [h2] at h1
    have : ((P.card * (Fintype.card V - P.card) : ℕ) : ℤ) =
        (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) := by push_cast [hpn]; ring
    have h1' : ((crossEdges G P).card : ℤ) ≤ ((P.card * (Fintype.card V - P.card) : ℕ) : ℤ) := by
      exact_mod_cast h1
    linarith
  refine ⟨hd, by linarith, by linarith, fun heq => ?_⟩
  rw [heq] at hcp
  have hm : (mCount G P : ℤ) = 0 := by linarith
  have hd0 : editDistance G P = 0 := by
    have : (editDistance G P : ℤ) = 0 := by linarith
    exact_mod_cast this
  unfold editDistance at hd0
  rw [card_eq_zero, SimpleGraph.edgeFinset_eq_empty] at hd0
  ext u v
  have := congrArg (fun H : SimpleGraph V => H.Adj u v) hd0
  simp only [SimpleGraph.bot_adj, eq_iff_iff, iff_false] at this
  rw [editGraph_adj] at this
  simp only [refGraph]
  tauto

end PaperVI

