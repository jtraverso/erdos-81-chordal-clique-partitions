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
Paper VI optimisation round — Priority 1: induced-`C₄` rigidity and quantitative
supersaturation.

The chordal core-rigidity argument (Lemma 6.1) only uses the absence of an induced `C₄`.
Here we prove:

* a nonuniform supersaturation inequality: the number `Z` of vertex sets inducing a `C₄` is at
  least the sum, over missing core pairs `ab`, of the number of nonadjacent pairs inside
  `W_ab = N(a) ∩ N(b) ∩ O`;
* the uniform consequence `2Z ≥ C (q - 2h)(q - 3h - 1)` whenever `2h ≤ q`;
* induced-`C₄`-free core rigidity under `3h + 2 ≤ q` (no relation between `p` and `n` needed);
* the corresponding exact formula `cp(G) = M(n) - A - 2m`, the stability estimate (21), and
  the quantitative correction `(q-2h)(q-3h-1)(cp(G) - M(n) + A + 2m) ≤ 2Z` in the setting of
  Theorem A. Chordality becomes a special case.
-/
module

public import PaperVI.Rigidity
public import Mathlib.Combinatorics.SimpleGraph.Copy

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` has no induced `4`-cycle. -/
def InducedC4Free (G : SimpleGraph V) : Prop :=
  IsEmpty (SimpleGraph.cycleGraph 4 ↪g G)

omit [Fintype V] [DecidableEq V] in
/-- Chordal graphs are induced-`C₄`-free. -/
theorem IsChordal.inducedC4Free {G : SimpleGraph V} (hG : IsChordal G) : InducedC4Free G :=
  hG 4 le_rfl

omit [Fintype V] [DecidableEq V] in
/-- Graphs with no (not necessarily induced) `4`-cycle are induced-`C₄`-free. -/
theorem inducedC4Free_of_free {G : SimpleGraph V} (hG : (SimpleGraph.cycleGraph 4).Free G) :
    InducedC4Free G :=
  ⟨fun f => hG ⟨f.toCopy⟩⟩

/-- A vertex set `S` induces a `4`-cycle: it is the image of an induced embedding of `C₄`. -/
def IsInducedC4Set (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ f : SimpleGraph.cycleGraph 4 ↪g G, Set.range f = (S : Set V)

open Classical in
/-- `Z(G)`: the number of unordered vertex sets inducing a `4`-cycle (each induced copy is
counted once, not once per automorphism of `C₄`). -/
noncomputable def inducedC4Count (G : SimpleGraph V) : ℕ :=
  ((univ : Finset (Finset V)).filter (IsInducedC4Set G)).card

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The missing core pairs (their number is `C`). -/
def missingCorePairs : Finset (Sym2 V) :=
  P.sym2.filter (fun e => ¬ e.IsDiag ∧ e ∉ G.edgeSet)

/-- `W_e = N(a) ∩ N(b) ∩ O` for a pair `e = ab`. -/
def commonExt (e : Sym2 V) : Finset V :=
  Pᶜ.filter (fun x => ∀ v ∈ e.toFinset, G.Adj v x)

/-- The nonadjacent (unordered, distinct) pairs inside a vertex set `X`. -/
def nonAdjPairs (X : Finset V) : Finset (Sym2 V) :=
  X.sym2.filter (fun e => ¬ e.IsDiag ∧ e ∉ G.edgeSet)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An induced `4`-cycle `a x b y`, together with its vertex set. -/
theorem isInducedC4Set_of {a x b y : V} (h1 : G.Adj a x) (h2 : G.Adj x b)
    (h3 : G.Adj b y) (h4 : G.Adj y a) (h5 : ¬ G.Adj a b) (h6 : ¬ G.Adj x y) (hab : a ≠ b)
    (hxy : x ≠ y) [DecidableEq V] : IsInducedC4Set G ({a, b} ∪ {x, y}) := by
  have hax := h1.ne; have hxb := h2.ne; have hby := h3.ne; have hya := h4.ne
  refine ⟨⟨⟨![a, x, b, y], ?_⟩, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · intro i j
    change G.Adj (![a, x, b, y] i) (![a, x, b, y] j) ↔ (SimpleGraph.cycleGraph 4).Adj i j
    rw [SimpleGraph.cycleGraph_adj]
    fin_cases i <;> fin_cases j <;> simp_all [G.adj_comm] <;> decide
  · ext v
    simp only [RelEmbedding.coe_mk, Set.mem_range, coe_union,
      coe_insert, coe_singleton, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      change ((![a, x, b, y] i = a ∨ ![a, x, b, y] i = b) ∨
        ![a, x, b, y] i = x ∨ ![a, x, b, y] i = y)
      fin_cases i <;> simp
    · rintro ((rfl | rfl) | (rfl | rfl))
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩

/-- **Nonuniform supersaturation.** `Σ_{ab missing core pair} #(nonadjacent pairs in W_ab) ≤ Z`.
Each such nonadjacent pair `xy` gives the induced `4`-cycle `a x b y`, and the vertex set
`{a,b,x,y}` determines `ab` (its core part) and `xy` (its exterior part). -/
theorem sum_card_nonAdjPairs_le_inducedC4Count :
    ∑ e ∈ missingCorePairs G P, (nonAdjPairs G (commonExt G P e)).card ≤ inducedC4Count G := by
  classical
  rw [← card_sigma]
  unfold inducedC4Count
  have hin : ∀ p ∈ (missingCorePairs G P).sigma (fun e => nonAdjPairs G (commonExt G P e)),
      (∀ v ∈ p.1, v ∈ P) ∧ (∀ v ∈ p.2, v ∉ P) := by
    intro p hp
    rw [mem_sigma] at hp
    obtain ⟨h0, h1⟩ := hp
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact mem_sym2_iff.mp (mem_filter.mp h0).1 v hv
    · have := mem_sym2_iff.mp (mem_filter.mp h1).1 v hv
      simpa using (mem_filter.mp this).1
  have hsplit : ∀ p ∈ (missingCorePairs G P).sigma (fun e => nonAdjPairs G (commonExt G P e)),
      (p.1.toFinset ∪ p.2.toFinset).filter (· ∈ P) = p.1.toFinset ∧
      (p.1.toFinset ∪ p.2.toFinset).filter (· ∉ P) = p.2.toFinset := by
    intro p hp
    obtain ⟨h1, h2⟩ := hin p hp
    constructor
    · ext v
      simp only [mem_filter, mem_union, Sym2.mem_toFinset]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact h
        · exact absurd hv (h2 v h)
      · intro h; exact ⟨Or.inl h, h1 v h⟩
    · ext v
      simp only [mem_filter, mem_union, Sym2.mem_toFinset]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact absurd (h1 v h) hv
        · exact h
      · intro h; exact ⟨Or.inr h, h2 v h⟩
  have hinj : ∀ e e' : Sym2 V, e.toFinset = e'.toFinset → e = e' := by
    intro e e' h
    refine Sym2.ext fun v => ?_
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, h]
  refine card_le_card_of_injOn (fun p => p.1.toFinset ∪ p.2.toFinset) ?_ ?_
  · intro p hp
    have hp' := hp
    rw [mem_coe, mem_sigma] at hp'
    obtain ⟨h0, h1⟩ := hp'
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    obtain ⟨e0, e⟩ := p
    dsimp only at h0 h1 ⊢
    induction e0 using Sym2.ind with
    | h a b =>
    induction e using Sym2.ind with
    | h x y =>
    simp only [missingCorePairs, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq] at h0
    simp only [nonAdjPairs, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq] at h1
    obtain ⟨-, hab, hnab⟩ := h0
    obtain ⟨⟨hx, hy⟩, hxy, hnxy⟩ := h1
    simp only [commonExt, mem_filter, Sym2.toFinset_mk_eq, mem_insert, mem_singleton,
      forall_eq_or_imp, forall_eq] at hx hy
    rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq]
    exact isInducedC4Set_of G hx.2.1 hx.2.2.symm hy.2.2 hy.2.1.symm hnab hnxy hab hxy
  · intro p hp p' hp' heq
    have heq' : p.1.toFinset ∪ p.2.toFinset = p'.1.toFinset ∪ p'.2.toFinset := heq
    obtain ⟨s1, s2⟩ := hsplit p hp
    obtain ⟨s1', s2'⟩ := hsplit p' hp'
    have e1 : p.1 = p'.1 := hinj _ _ (by rw [← s1, ← s1', heq'])
    have e2 : p.2 = p'.2 := hinj _ _ (by rw [← s2, ← s2', heq'])
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := p'
    dsimp only at e1 e2
    subst e1 e2
    rfl

/-- Inside a set `X ⊆ O` of size `w`, at least `w (w - 1 - h)/2` pairs are nonadjacent,
because every exterior vertex has at most `h` exterior neighbours. -/
theorem card_nonAdjPairs_ge (X : Finset V) (hX : X ⊆ Pᶜ) :
    (X.card : ℤ) * ((X.card : ℤ) - 1 - editDegree G P) ≤ 2 * (nonAdjPairs G X).card := by
  set D := X.sym2.filter (fun e => ¬ e.IsDiag) with hD
  have h1 := card_filter_add_card_filter_not (s := D) (fun e => e ∈ G.edgeSet)
  have h2 := card_sym2_filter_not_isDiag X
  have h3 : D.filter (fun e => e ∉ G.edgeSet) = nonAdjPairs G X := by
    rw [hD, filter_filter]; rfl
  set E := D.filter (fun e => e ∈ G.edgeSet) with hE
  have hmemE : ∀ x y : V, s(x, y) ∈ E ↔ (x ∈ X ∧ y ∈ X) ∧ x ≠ y ∧ G.Adj x y := by
    intro x y
    simp only [hE, hD, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq]
    tauto
  have hEcard : 2 * E.card ≤ X.card * editDegree G P := by
    have hinc : ∑ x ∈ X, (E.filter (fun e => x ∈ e)).card = 2 * E.card := by
      rw [sum_card_filter_comm, card_eq_sum_ones, mul_sum, mul_one]
      refine sum_congr rfl fun e he => ?_
      induction e using Sym2.ind with
      | h x y =>
        rw [hmemE] at he
        have : X.filter (fun z => z ∈ s(x, y)) = {x, y} := by
          ext z
          simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro (rfl | rfl)
            · exact ⟨he.1.1, Or.inl rfl⟩
            · exact ⟨he.1.2, Or.inr rfl⟩
        rw [this, card_pair he.2.1]
    rw [← hinc]
    calc ∑ x ∈ X, (E.filter (fun e => x ∈ e)).card ≤ ∑ _x ∈ X, editDegree G P := by
          refine sum_le_sum fun x hx => ?_
          have hxP : x ∉ P := by simpa using hX hx
          have hsub : E.filter (fun e => x ∈ e) ⊆ (extEdges G P).filter (fun e => x ∈ e) := by
            intro e he
            rw [mem_filter] at he ⊢
            refine ⟨?_, he.2⟩
            have he1 := he.1
            induction e using Sym2.ind with
            | h y z =>
              rw [hmemE] at he1
              rw [mem_extEdges]
              exact ⟨he1.2.2, by simpa using hX he1.1.1, by simpa using hX he1.1.2⟩
          exact (card_le_card hsub).trans ((card_extEdges_incident_le G P x).trans
            (le_trans (Nat.le_add_left _ _) (ext_local_bound G P x hxP)))
      _ = X.card * editDegree G P := by rw [sum_const, smul_eq_mul]
  rw [h3] at h1
  have hc := two_mul_choose_two X.card
  have h1Z : (E.card : ℤ) + (nonAdjPairs G X).card = X.card.choose 2 := by
    rw [← h2]; exact_mod_cast h1
  have hEZ : 2 * (E.card : ℤ) ≤ X.card * editDegree G P := by exact_mod_cast hEcard
  nlinarith

/-- For a missing core pair `ab`, `|W_ab| ≥ q - 2h`. -/
theorem card_commonExt_ge {e : Sym2 V} (he : e ∈ missingCorePairs G P) :
    Pᶜ.card ≤ (commonExt G P e).card + 2 * editDegree G P := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [missingCorePairs, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq] at he
    obtain ⟨⟨ha, hb⟩, -, -⟩ := he
    have hW : commonExt G P s(a, b) = Pᶜ.filter (fun x => G.Adj a x ∧ G.Adj b x) := by
      unfold commonExt
      refine filter_congr fun x _ => ?_
      simp [Sym2.toFinset_mk_eq]
    rw [hW]
    set X := Pᶜ.filter (fun x => G.Adj a x ∧ G.Adj b x)
    have hcov : Pᶜ ⊆ X ∪ Pᶜ.filter (fun x => ¬ G.Adj a x) ∪
        Pᶜ.filter (fun x => ¬ G.Adj b x) := by
      intro x hx
      by_cases h1 : G.Adj a x
      · by_cases h2 : G.Adj b x
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx, h1, h2⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨hx, h2⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx, h1⟩))
    have h1 := card_le_card hcov
    have h2 := card_union_le (X ∪ Pᶜ.filter (fun x => ¬ G.Adj a x))
      (Pᶜ.filter (fun x => ¬ G.Adj b x))
    have h3 := card_union_le X (Pᶜ.filter (fun x => ¬ G.Adj a x))
    have h4 := core_local_bound G P a ha
    have h5 := core_local_bound G P b hb
    omega

/-- The number of missing core pairs is `C`. -/
theorem card_missingCorePairs : ((missingCorePairs G P).card : ℤ) = Cdef G P := by
  have h1 := card_filter_add_card_filter_not (s := P.sym2.filter (fun e => ¬ e.IsDiag))
    (fun e => e ∈ G.edgeSet)
  have h2 := card_sym2_filter_not_isDiag P
  have h3 : (P.sym2.filter (fun e => ¬ e.IsDiag)).filter (fun e => e ∉ G.edgeSet) =
      missingCorePairs G P := by
    rw [filter_filter]; rfl
  have h4 : (P.sym2.filter (fun e => ¬ e.IsDiag)).filter (fun e => e ∈ G.edgeSet) =
      coreEdges G P := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_coreEdges]
      simp only [mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
        SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, -⟩, hadj⟩; exact ⟨hadj, ha, hb⟩
      · rintro ⟨hadj, ha, hb⟩; exact ⟨⟨⟨ha, hb⟩, hadj.ne⟩, hadj⟩
  rw [h3, h4, h2] at h1
  unfold Cdef uCount
  omega

/-- A missing core pair forces `h ≥ 1`. -/
theorem one_le_editDegree_of_missing {e : Sym2 V} (he : e ∈ missingCorePairs G P) :
    1 ≤ editDegree G P := by
  induction e using Sym2.ind with
  | h a b =>
    simp only [missingCorePairs, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq] at he
    obtain ⟨⟨ha, -⟩, hab, hnot⟩ := he
    have := card_le_editDegree G P a {b} (fun w hw => by
      rw [mem_singleton] at hw; subst hw
      rw [editGraph_adj]; right; exact ⟨⟨hab, Or.inl ha⟩, hnot⟩)
    simpa using this

/-- Elementary monotonicity: if `w ≥ A ≥ 0` then
`max(0, w(w-1-h)) ≥ A(A-1-h)`, in the form used below. -/
theorem int_aux_mono {w A h N : ℤ} (hA : 0 ≤ A) (hw : A ≤ w) (hN : 0 ≤ N)
    (hwN : w * (w - 1 - h) ≤ N) : A * (A - 1 - h) ≤ N := by
  rcases le_or_gt A (h + 1) with h1 | h1
  · nlinarith
  · nlinarith

/-- **Uniform supersaturation.** If `2h ≤ q`, then `2Z ≥ C (q - 2h)(q - 3h - 1)`
(integer arithmetic; for `q ≤ 3h + 1` the right side is `≤ 0`). -/
theorem inducedC4Count_ge (hq : 2 * editDegree G P ≤ Pᶜ.card) :
    Cdef G P * (((Pᶜ.card : ℤ) - 2 * editDegree G P) *
      ((Pᶜ.card : ℤ) - 3 * editDegree G P - 1)) ≤ 2 * inducedC4Count G := by
  have hsum := sum_card_nonAdjPairs_le_inducedC4Count G P
  rw [← card_missingCorePairs, ← nsmul_eq_mul, ← sum_const]
  have hsumZ : (2 : ℤ) * ∑ e ∈ missingCorePairs G P, ((nonAdjPairs G (commonExt G P e)).card : ℤ)
      ≤ 2 * inducedC4Count G := by
    have : (∑ e ∈ missingCorePairs G P, ((nonAdjPairs G (commonExt G P e)).card : ℤ)) ≤
        inducedC4Count G := by exact_mod_cast hsum
    linarith
  refine le_trans ?_ hsumZ
  rw [mul_sum]
  refine sum_le_sum fun e he => ?_
  have hw := card_commonExt_ge G P he
  have hN := card_nonAdjPairs_ge G P (commonExt G P e) (filter_subset _ _)
  have hwZ : (Pᶜ.card : ℤ) - 2 * editDegree G P ≤ (commonExt G P e).card := by
    have : (Pᶜ.card : ℤ) ≤ (commonExt G P e).card + 2 * editDegree G P := by exact_mod_cast hw
    linarith
  have hqZ : (2 : ℤ) * editDegree G P ≤ Pᶜ.card := by exact_mod_cast hq
  have := int_aux_mono (A := (Pᶜ.card : ℤ) - 2 * editDegree G P) (by linarith) hwZ
    (by positivity) hN
  have e1 : (Pᶜ.card : ℤ) - 3 * editDegree G P - 1 =
      ((Pᶜ.card : ℤ) - 2 * editDegree G P) - 1 - editDegree G P := by ring
  rw [e1]
  exact this

/-- **Nonuniform supersaturation, numerical form.**
`Σ_{ab missing core pair} |W_ab| (|W_ab| - 1 - h) ≤ 2Z`, with `W_ab = N(a) ∩ N(b) ∩ O`. -/
theorem sum_commonExt_le_inducedC4Count :
    ∑ e ∈ missingCorePairs G P, ((commonExt G P e).card : ℤ) *
      (((commonExt G P e).card : ℤ) - 1 - editDegree G P) ≤ 2 * inducedC4Count G := by
  have hsum := sum_card_nonAdjPairs_le_inducedC4Count G P
  have hsumZ : (∑ e ∈ missingCorePairs G P, ((nonAdjPairs G (commonExt G P e)).card : ℤ)) ≤
      inducedC4Count G := by exact_mod_cast hsum
  calc ∑ e ∈ missingCorePairs G P, ((commonExt G P e).card : ℤ) *
        (((commonExt G P e).card : ℤ) - 1 - editDegree G P)
      ≤ ∑ e ∈ missingCorePairs G P, 2 * ((nonAdjPairs G (commonExt G P e)).card : ℤ) :=
        sum_le_sum fun e _ => card_nonAdjPairs_ge G P _ (filter_subset _ _)
    _ ≤ 2 * inducedC4Count G := by rw [← mul_sum]; linarith

/-- **Induced-`C₄`-free core rigidity.** If `G` has no induced `4`-cycle and either `h = 0`
or `3h + 2 ≤ q`, then the core is complete. No relation between `p` and `n` is used. -/
theorem core_complete_of_inducedC4Free
    (hq : editDegree G P = 0 ∨ 3 * editDegree G P + 2 ≤ Pᶜ.card) (hG : InducedC4Free G) :
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → G.Adj a b := by
  classical
  intro a ha b hb hab
  by_contra hnot
  have he : s(a, b) ∈ missingCorePairs G P := by
    simp only [missingCorePairs, mem_filter, mem_sym2_iff, Sym2.mem_iff, Sym2.mk_isDiag_iff,
      SimpleGraph.mem_edgeSet, forall_eq_or_imp, forall_eq]
    exact ⟨⟨ha, hb⟩, hab, hnot⟩
  have h1 := one_le_editDegree_of_missing G P he
  have hq' : 3 * editDegree G P + 2 ≤ Pᶜ.card := hq.resolve_left (by omega)
  have hw := card_commonExt_ge G P he
  have hN := card_nonAdjPairs_ge G P (commonExt G P s(a, b)) (filter_subset _ _)
  have hpos : 0 < (nonAdjPairs G (commonExt G P s(a, b))).card := by
    have hwZ : (editDegree G P : ℤ) + 2 ≤ (commonExt G P s(a, b)).card := by
      have : (Pᶜ.card : ℤ) ≤ (commonExt G P s(a, b)).card + 2 * editDegree G P := by
        exact_mod_cast hw
      have : (3 * editDegree G P + 2 : ℤ) ≤ Pᶜ.card := by exact_mod_cast hq'
      linarith
    have : (0 : ℤ) < (nonAdjPairs G (commonExt G P s(a, b))).card := by nlinarith
    exact_mod_cast this
  have hsum := sum_card_nonAdjPairs_le_inducedC4Count G P
  have hZ : 0 < inducedC4Count G :=
    lt_of_lt_of_le (lt_of_lt_of_le hpos (single_le_sum
      (f := fun e => (nonAdjPairs G (commonExt G P e)).card) (fun _ _ => Nat.zero_le _) he)) hsum
  unfold inducedC4Count at hZ
  obtain ⟨S, hS⟩ := card_pos.mp hZ
  obtain ⟨f, -⟩ := (mem_filter.mp hS).2
  exact hG.false f

/-- Under induced-`C₄`-freeness and `h = 0 ∨ 3h + 2 ≤ q`, `C = 0`. -/
theorem Cdef_eq_zero_of_inducedC4Free
    (hq : editDegree G P = 0 ∨ 3 * editDegree G P + 2 ≤ Pᶜ.card) (hG : InducedC4Free G) :
    Cdef G P = 0 := by
  have hcore := core_complete_of_inducedC4Free G P hq hG
  unfold Cdef uCount
  have : coreEdges G P = innerEdges G P := rfl
  rw [this, card_innerEdges_of_isClique G P (fun a ha b hb hab => hcore a ha b hb hab)]
  ring

/-- **Exact formula for induced-`C₄`-free graphs (generalising (20)).** In the setting of
Theorem A (`n ≥ 2`, `p = ⌊(n+1)/3⌋`, `p ≥ 18h + 1`), an induced-`C₄`-free graph has `C = 0`
and `cp(G) = M(n) - A - 2m`. -/
theorem cp_inducedC4Free (hn : 2 ≤ Fintype.card V) (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) (hG : InducedC4Free G) :
    Cdef G P = 0 ∧ (cp G : ℤ) = Mval (Fintype.card V) - Adef G P - 2 * mCount G P := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  have hC : Cdef G P = 0 := by
    refine Cdef_eq_zero_of_inducedC4Free G P ?_ hG
    rcases Nat.eq_zero_or_pos (editDegree G P) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by omega)
  refine ⟨hC, ?_⟩
  have := (theoremA G P hn hP hh).1
  rw [this, hC]; ring

/-- **Quantitative correction to `cp(G) = M(n) - A - 2m`.** In the setting of Theorem A,
`(q - 2h)(q - 3h - 1) · (cp(G) - M(n) + A + 2m) ≤ 2Z`, where `Z` is the number of induced
`4`-cycles; here `cp(G) - M(n) + A + 2m = C`. -/
theorem cp_correction_inducedC4 (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 18 * editDegree G P + 1 ≤ P.card) :
    (((Pᶜ.card : ℤ) - 2 * editDegree G P) * ((Pᶜ.card : ℤ) - 3 * editDegree G P - 1)) *
      ((cp G : ℤ) - Mval (Fintype.card V) + Adef G P + 2 * mCount G P) ≤
        2 * inducedC4Count G := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  have hcp := (theoremA G P hn hP hh).1
  have h := inducedC4Count_ge G P (by omega)
  have : (cp G : ℤ) - Mval (Fintype.card V) + Adef G P + 2 * mCount G P = Cdef G P := by
    rw [hcp]; ring
  rw [this, mul_comm]
  exact h

/-- **Stability (21) for induced-`C₄`-free graphs.** In the setting of Theorem A, an
induced-`C₄`-free graph satisfies `d_edit = A + m`, `d_edit ≤ M(n) - cp(G) ≤ 2 d_edit`, and
`cp(G) = M(n)` forces `G = K_P ∨ I_O`. -/
theorem inducedC4Free_stability (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) (hG : InducedC4Free G) :
    (editDistance G P : ℤ) = Adef G P + mCount G P ∧
    (editDistance G P : ℤ) ≤ Mval (Fintype.card V) - cp G ∧
    (Mval (Fintype.card V) : ℤ) - cp G ≤ 2 * editDistance G P ∧
    (cp G = Mval (Fintype.card V) → G = refGraph P) := by
  obtain ⟨hC, hcp⟩ := cp_inducedC4Free G P hn hP hh hG
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
