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

module

public import PaperV.TerminalPairRounding
public import PaperV.Vizing.Main
public import PaperV.BeckFiala

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.Tauto

@[expose] public section

/-!
# P4-133 assembly: F_S ↔ lineGraph glue  (per researcher V3528)

Chain: Beck–Fiala (row-discrepancy `< 5` on the two unordered incidence rows `R_{i,w}` +
global row) → degree bound `Δ(F_S) ≤ a+9` → Vizing (`F_S` is `(a+10)`-edge-colourable) →
Layer 3 (delete 10 classes, loss `≤ 10·|X|`) → `⌊a·|Pall|/m⌋ ≤ |S'| + 4 + 10·|X|`.

NB (V3528 §0/§8): formal Beck–Fiala gives strict `< 5`, NOT `≤ 4`; the existence proof must
use the `< 5` output on the unordered `(i,w)` rows (two per vertex), giving `Δ ≤ a+9`. Layer 2
(`incDeg_le_of_discrepancy`) stays a valid *conditional* interface but is NOT used here.
-/

open Finset SimpleGraph

namespace PaperV.TerminalPair

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]

/-- Terminal graph of a selection `S`: vertices `B`, edges the terminal pairs of objects in `S`. -/
def termGraph (emap : ι → Fin 2 → Sym2 B) (S : Finset ι) : SimpleGraph B :=
  SimpleGraph.fromEdgeSet {e : Sym2 B | ∃ P ∈ S, ∃ i : Fin 2, emap P i = e ∧ ¬ e.IsDiag}

instance (emap : ι → Fin 2 → Sym2 B) (S : Finset ι) :
    DecidableRel (termGraph emap S).Adj := by
  classical unfold termGraph; infer_instance

/-- Unordered incidence row: objects one of whose `i`-th terminal edge is incident to `w`. -/
def incRow (emap : ι → Fin 2 → Sym2 B) (S : Finset ι) (i : Fin 2) (w : B) : Finset ι :=
  S.filter (fun P => w ∈ emap P i)

omit [Fintype ι] in
/-- Local form of the degree bridge: the hypotheses are only needed on `S`. -/
theorem termGraph_degree_eq_of_mem
    (emap : ι → Fin 2 → Sym2 B) (S : Finset ι)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ S})
    (hloop : ∀ P ∈ S, ∀ i, ¬ (emap P i).IsDiag)
    (w : B) :
    (termGraph emap S).degree w
      = (incRow emap S 0 w).card + (incRow emap S 1 w).card := by
  classical
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  set T : Finset (ι × Fin 2) :=
    ((incRow emap S 0 w).image (fun P => (P, (0 : Fin 2)))) ∪
      ((incRow emap S 1 w).image (fun P => (P, (1 : Fin 2)))) with hT
  have hmemT : ∀ p ∈ T, p.1 ∈ S ∧ w ∈ emap p.1 p.2 := by
    rintro ⟨P, i⟩ hp
    simp only [hT, Finset.mem_union, Finset.mem_image, incRow, Finset.mem_filter,
      Prod.mk.injEq] at hp
    rcases hp with ⟨Q, ⟨hQ, hw⟩, hQ1, hQ2⟩ | ⟨Q, ⟨hQ, hw⟩, hQ1, hQ2⟩ <;>
      · subst hQ1; subst hQ2; exact ⟨hQ, hw⟩
  have himg : (termGraph emap S).incidenceFinset w = T.image (fun p => emap p.1 p.2) := by
    ext e
    simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, Set.mem_setOf_eq,
      Finset.mem_image]
    constructor
    · rintro ⟨he, hw⟩
      rw [termGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
      obtain ⟨⟨P, hP, i, hPi, -⟩, -⟩ := he
      refine ⟨(P, i), ?_, hPi⟩
      subst hPi
      simp only [hT, Finset.mem_union, Finset.mem_image, incRow, Finset.mem_filter]
      fin_cases i
      · exact Or.inl ⟨P, ⟨hP, hw⟩, rfl⟩
      · exact Or.inr ⟨P, ⟨hP, hw⟩, rfl⟩
    · rintro ⟨⟨P, i⟩, hp, rfl⟩
      obtain ⟨hPS, hw⟩ := hmemT _ hp
      refine ⟨?_, hw⟩
      rw [termGraph, SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨⟨P, hPS, i, rfl, hloop P hPS i⟩, by simpa [Sym2.diagSet] using hloop P hPS i⟩
  have hinjT : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) T := by
    intro p hp q hq h
    exact hinj (hmemT p hp).1 (hmemT q hq).1 h
  rw [himg, Finset.card_image_of_injOn hinjT, hT, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  · simp only [Finset.disjoint_left, Finset.mem_image]
    rintro x ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    simp at hb

omit [Fintype ι] in
/-- **Degree bridge.** The `SimpleGraph` degree of `termGraph emap S` at `w` equals the sum of
the two unordered incidence rows at `w`, provided edges are physically distinct (`hinj`) and
loopless (`hloop`). -/
theorem termGraph_degree_eq
    (emap : ι → Fin 2 → Sym2 B)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | True})
    (hloop : ∀ P i, ¬ (emap P i).IsDiag)
    (S : Finset ι) (w : B) :
    (termGraph emap S).degree w
      = (incRow emap S 0 w).card + (incRow emap S 1 w).card :=
  termGraph_degree_eq_of_mem emap S (fun _ _ _ _ h => hinj (by trivial) (by trivial) h)
    (fun P _ i => hloop P i) w

omit [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B] in
/-- Membership in the edge set of a terminal graph. -/
theorem mem_termGraph_edgeSet (emap : ι → Fin 2 → Sym2 B) (S : Finset ι) (e : Sym2 B) :
    e ∈ (termGraph emap S).edgeSet ↔ (∃ P ∈ S, ∃ i : Fin 2, emap P i = e) ∧ ¬ e.IsDiag := by
  rw [termGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨P, hP, i, hPi, hd⟩, -⟩
    exact ⟨⟨P, hP, i, hPi⟩, hd⟩
  · rintro ⟨⟨P, hP, i, hPi⟩, hd⟩
    exact ⟨⟨P, hP, i, hPi, hd⟩, by simpa [Sym2.diagSet] using hd⟩

omit [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B] in
/-- Edge sets of terminal graphs are monotone in the selection. -/
theorem termGraph_edgeSet_mono (emap : ι → Fin 2 → Sym2 B) {S S' : Finset ι} (h : S' ⊆ S) :
    (termGraph emap S').edgeSet ⊆ (termGraph emap S).edgeSet := by
  intro e he
  rw [termGraph, SimpleGraph.edgeSet_fromEdgeSet] at he ⊢
  obtain ⟨⟨P, hP, i, hPi, hd⟩, hd'⟩ := he
  exact ⟨⟨P, h hP, i, hPi, hd⟩, hd'⟩

omit [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B] in
/-- Terminal edges of selected objects are edges of the terminal graph. -/
theorem emap_mem_edgeSet (emap : ι → Fin 2 → Sym2 B) {S : Finset ι} {P : ι} (hP : P ∈ S)
    (hloop : ¬ (emap P i).IsDiag) : emap P i ∈ (termGraph emap S).edgeSet := by
  rw [termGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨⟨P, hP, i, rfl, hloop⟩, by simpa [Sym2.diagSet] using hloop⟩

omit [Fintype ι] in
/-- **Beck–Fiala selection.**  Rounding the constant fractional solution `x ≡ a/m` on the
five-row incidence system (two unordered rows `R_{i,w}` per vertex, plus the global row)
gives a selection `S ⊆ Pall` with discrepancy `< 5` on every row. -/
theorem exists_selection (emap : ι → Fin 2 → Sym2 B) (Pall : Finset ι) (a m : ℕ)
    (ha1 : 1 ≤ a) (ham : a ≤ m) :
    ∃ S ⊆ Pall,
      (∀ (i : Fin 2) (w : B),
          ((incRow emap S i w).card : ℚ)
            < (a : ℚ) / m * ((incRow emap Pall i w).card : ℚ) + 5) ∧
        (a : ℚ) / m * (Pall.card : ℚ) < (S.card : ℚ) + 5 := by
  classical
  have hm : 0 < m := lt_of_lt_of_le ha1 ham
  have hmQ : (0:ℚ) < (m:ℚ) := by exact_mod_cast hm
  set N := Pall.card with hN
  set ee : {x // x ∈ Pall} ≃ Fin N := Pall.equivFin with hee
  set M := Fintype.card (Option (Fin 2 × B)) with hM
  set re : Option (Fin 2 × B) ≃ Fin M := Fintype.equivFin _ with hre
  set rowInd : Option (Fin 2 × B) → ι → ℤ := fun r P =>
    match r with
    | none => 1
    | some q => if q.2 ∈ emap P q.1 then 1 else 0 with hrowInd
  set A : Fin M → Fin N → ℤ := fun j i => rowInd (re.symm j) ((ee.symm i : ι)) with hA'
  have hA : ∀ j i, A j i = 0 ∨ A j i = 1 := by
    intro j i
    simp only [hA', hrowInd]
    rcases (re.symm j) with _ | q
    · exact Or.inr rfl
    · by_cases h : q.2 ∈ emap ((ee.symm i : ι)) q.1 <;> simp [h]
  have hdeg : ∀ i, (univ.filter (fun j => A j i = 1)).card ≤ 5 := by
    intro i
    set P : ι := (ee.symm i : ι) with hP
    have hcard : (univ.filter (fun j : Fin M => A j i = 1)).card
        = (univ.filter (fun r : Option (Fin 2 × B) => rowInd r P = 1)).card := by
      refine Finset.card_equiv re.symm ?_
      intro j; simp [hA', hP]
    rw [hcard]
    have hsub : (univ.filter (fun r : Option (Fin 2 × B) => rowInd r P = 1)) ⊆
        insert none
          (((univ.filter (fun w : B => w ∈ emap P 0)).image (fun w => some ((0 : Fin 2), w))) ∪
            ((univ.filter (fun w : B => w ∈ emap P 1)).image
              (fun w => some ((1 : Fin 2), w)))) := by
      rintro (_ | ⟨k, w⟩) hr
      · exact Finset.mem_insert_self _ _
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrowInd] at hr
        by_cases hw : w ∈ emap P k
        · refine Finset.mem_insert_of_mem ?_
          rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
          · exact Finset.mem_union_left _ (by simp [hw])
          · exact Finset.mem_union_right _ (by simp [hw])
        · simp [hw] at hr
    have hb2 : ∀ k : Fin 2, ((univ.filter (fun w : B => w ∈ emap P k)).image
        (fun w => some ((k : Fin 2), w))).card ≤ 2 := by
      intro k
      refine le_trans (Finset.card_image_le) ?_
      induction (emap P k) using Sym2.ind with
      | _ x y =>
        refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({x, y} : Finset B))) ?_
        · intro w hw; simp at hw ⊢; tauto
        · exact le_trans (Finset.card_insert_le _ _) (by simp)
    calc (univ.filter (fun r : Option (Fin 2 × B) => rowInd r P = 1)).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ 1 + (2 + 2) := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          have := Finset.card_union_le
            ((univ.filter (fun w : B => w ∈ emap P 0)).image (fun w => some ((0 : Fin 2), w)))
            ((univ.filter (fun w : B => w ∈ emap P 1)).image (fun w => some ((1 : Fin 2), w)))
          have h0 := hb2 0
          have h1 := hb2 1
          omega
      _ = 5 := by norm_num
  set xx : Fin N → ℚ := fun _ => (a:ℚ)/m with hxx
  have hx : ∀ i, 0 ≤ xx i ∧ xx i ≤ 1 := by
    intro i
    refine ⟨by positivity, ?_⟩
    rw [hxx, div_le_one hmQ]
    exact_mod_cast ham
  obtain ⟨y, hy01, hbd⟩ := _root_.beck_fiala (by norm_num : (1:ℕ) ≤ 5) A hA hdeg xx hx
  set S : Finset ι := (Pall.attach.filter (fun P => y (ee P) = 1)).image Subtype.val with hS
  have hSsub : S ⊆ Pall := by
    intro P hP
    simp only [hS, Finset.mem_image, Finset.mem_filter] at hP
    obtain ⟨Q, -, rfl⟩ := hP
    exact Q.2
  have hmemS : ∀ (Q : {x // x ∈ Pall}), (Q : ι) ∈ S ↔ y (ee Q) = 1 := by
    intro Q
    simp only [hS, Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and,
      Subtype.exists]
    constructor
    · rintro ⟨R, hR, hy, hRQ⟩
      have hRQ' : (⟨R, hR⟩ : {x // x ∈ Pall}) = Q := Subtype.ext hRQ
      rwa [hRQ'] at hy
    · intro h
      exact ⟨Q.1, Q.2, by simpa using h, rfl⟩
  have key : ∀ r : Option (Fin 2 × B),
      ∑ i : Fin N, ((A (re r) i : ℚ)) * ((y i : ℚ) - xx i)
        = ∑ P ∈ Pall, ((rowInd r P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m) := by
    intro r
    have step1 : ∑ i : Fin N, ((A (re r) i : ℚ)) * ((y i : ℚ) - xx i)
        = ∑ Q : {x // x ∈ Pall},
            ((rowInd r (Q:ι) : ℚ)) * ((y (ee Q) : ℚ) - (a:ℚ)/m) := by
      rw [← Equiv.sum_comp ee.symm
        (fun Q : {x // x ∈ Pall} => ((rowInd r (Q:ι) : ℚ)) * ((y (ee Q) : ℚ) - (a:ℚ)/m))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [hA', hxx, Equiv.apply_symm_apply]
    rw [step1, ← Finset.sum_attach Pall
      (fun P => ((rowInd r P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m))]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    congr 2
    rcases hy01 (ee Q) with h | h
    · have hns : ¬ ((Q:ι) ∈ S) := by rw [hmemS Q, h]; norm_num
      rw [h]; simp [hns]
    · have hs : ((Q:ι) ∈ S) := by rw [hmemS Q, h]
      rw [h]; simp [hs]
  have hfilterS : ∀ (i : Fin 2) (w : B),
      (Pall.filter (fun P => w ∈ emap P i)).filter (fun P => P ∈ S) = incRow emap S i w := by
    intro i w
    ext P
    simp only [Finset.mem_filter, incRow]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hSsub h.1, h.2⟩, h.1⟩⟩
  have hsumrow : ∀ (i : Fin 2) (w : B),
      ∑ P ∈ Pall, ((rowInd (some (i,w)) P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m)
        = ((incRow emap S i w).card : ℚ) - (a:ℚ)/m * ((incRow emap Pall i w).card : ℚ) := by
    intro i w
    have hpt : ∀ P : ι, ((rowInd (some (i,w)) P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m)
        = if w ∈ emap P i then ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m) else 0 := by
      intro P
      simp only [hrowInd]
      split <;> simp
    rw [Finset.sum_congr rfl (fun P _ => hpt P), ← Finset.sum_filter, Finset.sum_sub_distrib,
      Finset.sum_boole, Finset.sum_const, nsmul_eq_mul, hfilterS i w]
    simp only [incRow]
    ring
  have hsumnone :
      ∑ P ∈ Pall, ((rowInd none P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m)
        = (S.card : ℚ) - (a:ℚ)/m * (Pall.card : ℚ) := by
    have hpt : ∀ P : ι, ((rowInd none P : ℚ)) * ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m)
        = ((if P ∈ S then (1:ℚ) else 0) - (a:ℚ)/m) := by
      intro P; simp [hrowInd]
    rw [Finset.sum_congr rfl (fun P _ => hpt P), Finset.sum_sub_distrib, Finset.sum_boole,
      Finset.sum_const, nsmul_eq_mul]
    have hPS : Pall.filter (fun P => P ∈ S) = S := by
      ext P; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hSsub h, h⟩⟩
    rw [hPS]; ring
  refine ⟨S, hSsub, ?_, ?_⟩
  · intro i w
    have h := hbd (re (some (i, w)))
    rw [key, hsumrow] at h
    rw [abs_lt] at h
    have h2 := h.2
    push_cast at h2
    linarith
  · have h := hbd (re none)
    rw [key, hsumnone] at h
    rw [abs_lt] at h
    have h1 := h.1
    push_cast at h1
    linarith

/-- **P4-133 (existence, assembled) — V3528 §7 recommended signature.** -/
theorem p4_133_existence
    (emap : ι → Fin 2 → Sym2 B)
    (Pall : Finset ι)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ Pall})
    (hloop : ∀ P ∈ Pall, ∀ i, ¬ (emap P i).IsDiag)
    (a m : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m)
    (X : Finset B)
    (hcover : ∀ P ∈ Pall, ∀ i, ∃ w ∈ X, w ∈ emap P i)
    (hbaseDeg : (termGraph emap Pall).maxDegree ≤ m) :
    ∃ S' : Finset ι,
      S' ⊆ Pall ∧
      ((termGraph emap S').lineGraph).Colorable a ∧
      (a * Pall.card) / m ≤ S'.card + 4 + 10 * X.card := by
  classical
  have hm : 0 < m := lt_of_lt_of_le ha1 ham
  have hmQ : (0:ℚ) < (m:ℚ) := by exact_mod_cast hm
  obtain ⟨S, hSsub, hrow, hglob⟩ := exists_selection emap Pall a m ha1 ham
  have hinjS : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ S} :=
    fun p hp q hq h => hinj (hSsub hp) (hSsub hq) h
  have hloopS : ∀ P ∈ S, ∀ i, ¬ (emap P i).IsDiag := fun P hP i => hloop P (hSsub hP) i
  -- Degree bound `Δ(F_S) ≤ a + 9` from the two unordered rows.
  have hmax : (termGraph emap S).maxDegree ≤ a + 9 := by
    refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ (fun w => ?_)
    have hdS := termGraph_degree_eq_of_mem emap S hinjS hloopS w
    have hdP := termGraph_degree_eq_of_mem emap Pall hinj hloop w
    have hbase : (termGraph emap Pall).degree w ≤ m :=
      le_trans (SimpleGraph.degree_le_maxDegree _ _) hbaseDeg
    have hbQ : ((incRow emap Pall 0 w).card : ℚ) + ((incRow emap Pall 1 w).card : ℚ) ≤ (m:ℚ) := by
      rw [hdP] at hbase
      exact_mod_cast hbase
    have hfrac : (0:ℚ) ≤ (a:ℚ)/m := by positivity
    have hmul : (a:ℚ)/m * (((incRow emap Pall 0 w).card : ℚ)
        + ((incRow emap Pall 1 w).card : ℚ)) ≤ (a:ℚ)/m * (m:ℚ) :=
      mul_le_mul_of_nonneg_left hbQ hfrac
    rw [div_mul_cancel₀ _ (ne_of_gt hmQ)] at hmul
    have h0 := hrow 0 w
    have h1 := hrow 1 w
    have hQ : ((termGraph emap S).degree w : ℚ) < (a:ℚ) + 10 := by
      rw [hdS]; push_cast; linarith
    have hN : (termGraph emap S).degree w < a + 10 := by exact_mod_cast hQ
    omega
  -- Vizing: `F_S` is `(a+10)`-edge-colourable.
  obtain ⟨C⟩ : ((termGraph emap S).lineGraph).Colorable (a + 10) :=
    (Vizing.lineGraph_colorable (termGraph emap S)).mono (by omega)
  have hmemE : ∀ P ∈ S, ∀ i, emap P i ∈ (termGraph emap S).edgeSet :=
    fun P hP i => emap_mem_edgeSet emap hP (hloopS P hP i)
  set col : ι → Fin 2 → Fin (a + 10) := fun P i =>
    if h : emap P i ∈ (termGraph emap S).edgeSet then C ⟨emap P i, h⟩ else ⟨0, by omega⟩
    with hcoldef
  have hcolval : ∀ (P : ι) (i : Fin 2) (h : emap P i ∈ (termGraph emap S).edgeSet),
      col P i = C ⟨emap P i, h⟩ := by
    intro P i h
    simp [hcoldef, h]
  -- Ten removed colour classes.
  set D : Finset (Fin (a + 10)) :=
    univ \ ((univ : Finset (Fin a)).image (Fin.castLE (by omega))) with hDdef
  have hDcard : D.card = (a + 10) - a := by
    rw [hDdef, Finset.card_univ_diff,
      Finset.card_image_of_injective _ (Fin.castLE_injective _)]
    simp
  -- Each colour class meets at most `|X|` objects of `S`.
  have hclass : ∀ k : Fin (a + 10),
      (S.filter (fun P => col P 0 = k ∨ col P 1 = k)).card ≤ X.card := by
    intro k
    set T := S.filter (fun P => col P 0 = k ∨ col P 1 = k) with hT
    rcases T.eq_empty_or_nonempty with hTe | ⟨P₀, hP₀⟩
    · simp [hTe]
    obtain ⟨w₀, hw₀X, -⟩ := hcover P₀ (hSsub (Finset.mem_of_mem_filter _ hP₀)) 0
    haveI : Nonempty B := ⟨w₀⟩
    have hwit : ∀ P ∈ T, ∃ w, w ∈ X ∧ ∃ i : Fin 2, w ∈ emap P i ∧ col P i = k := by
      intro P hP
      rw [hT, Finset.mem_filter] at hP
      obtain ⟨hPS, hk⟩ := hP
      rcases hk with hk | hk
      · obtain ⟨w, hwX, hw⟩ := hcover P (hSsub hPS) 0; exact ⟨w, hwX, 0, hw, hk⟩
      · obtain ⟨w, hwX, hw⟩ := hcover P (hSsub hPS) 1; exact ⟨w, hwX, 1, hw, hk⟩
    choose! f hfX idx hfmem hfcol using hwit
    refine Finset.card_le_card_of_injOn f (fun P hP => hfX P hP) ?_
    intro P hP Q hQ hfe
    by_contra hne
    have hPS : P ∈ S := (Finset.mem_filter.1 hP).1
    have hQS : Q ∈ S := (Finset.mem_filter.1 hQ).1
    have hedgeP := hmemE P hPS (idx P)
    have hedgeQ := hmemE Q hQS (idx Q)
    have hdist : emap P (idx P) ≠ emap Q (idx Q) := by
      intro h
      exact hne (congrArg Prod.fst
        (hinj (show ((P, idx P) : ι × Fin 2).1 ∈ Pall from hSsub hPS)
          (show ((Q, idx Q) : ι × Fin 2).1 ∈ Pall from hSsub hQS) h))
    have hadj : ((termGraph emap S).lineGraph).Adj ⟨_, hedgeP⟩ ⟨_, hedgeQ⟩ := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨fun h => hdist (Subtype.mk_eq_mk.mp h), f P, hfmem P hP, ?_⟩
      rw [hfe]; exact hfmem Q hQ
    have hCne := C.valid hadj
    rw [← hcolval P (idx P) hedgeP, ← hcolval Q (idx Q) hedgeQ] at hCne
    exact hCne (by rw [hfcol P hP, hfcol Q hQ])
  -- Layer 3: delete the ten classes.
  obtain ⟨S', hS'sub, havoid, hpal, hloss⟩ :=
    extract_a_edge_colorable S (a + 10) a X.card col D (by omega) hDcard (fun k _ => hclass k)
  refine ⟨S', hS'sub.trans hSsub, ?_, ?_⟩
  · -- The surviving subfamily is `a`-edge-colourable.
    have hsub := termGraph_edgeSet_mono emap hS'sub
    have hin : ∀ v : ↥(termGraph emap S').edgeSet,
        C ⟨(v : Sym2 B), hsub v.2⟩ ∈ (univ : Finset (Fin (a + 10))) \ D := by
      intro v
      have hv : (v : Sym2 B) ∈ (termGraph emap S').edgeSet := v.2
      rw [mem_termGraph_edgeSet] at hv
      obtain ⟨⟨P, hP, i, hPi⟩, -⟩ := hv
      have hmem : emap P i ∈ (termGraph emap S).edgeSet := by
        rw [hPi]; exact hsub v.2
      have heq : (⟨(v : Sym2 B), hsub v.2⟩ : ↥(termGraph emap S).edgeSet) = ⟨emap P i, hmem⟩ :=
        Subtype.ext hPi.symm
      rw [heq, ← hcolval P i hmem]
      exact havoid P hP i
    set eqv := Finset.equivFinOfCardEq hpal with heqv
    refine ⟨SimpleGraph.Coloring.mk (fun v => eqv ⟨C ⟨(v : Sym2 B), hsub v.2⟩, hin v⟩) ?_⟩
    intro u v huv
    rw [SimpleGraph.lineGraph_adj_iff_exists] at huv
    obtain ⟨hne, x, hxu, hxv⟩ := huv
    have hadj : ((termGraph emap S).lineGraph).Adj
        ⟨(u : Sym2 B), hsub u.2⟩ ⟨(v : Sym2 B), hsub v.2⟩ := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨fun h => hne (Subtype.ext (Subtype.mk_eq_mk.mp h)), x, hxu, hxv⟩
    intro hcontra
    exact C.valid hadj (congrArg Subtype.val (eqv.injective hcontra))
  · -- Counting: the global row plus the Layer-3 loss.
    have hSnat : a * Pall.card < m * (S.card + 5) := by
      have hQ : (a:ℚ) * (Pall.card:ℚ) < (m:ℚ) * ((S.card:ℚ) + 5) := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hmQ] at hglob
        linarith
      exact_mod_cast hQ
    have hq : a * Pall.card / m ≤ S.card + 4 := by
      have h1 : (a * Pall.card / m) * m ≤ a * Pall.card := Nat.div_mul_le_self _ _
      have h2 : (a * Pall.card / m) * m < (S.card + 5) * m := by
        calc (a * Pall.card / m) * m ≤ a * Pall.card := h1
          _ < m * (S.card + 5) := hSnat
          _ = (S.card + 5) * m := by ring
      have := Nat.lt_of_mul_lt_mul_right h2
      omega
    have hD10 : D.card = 10 := by omega
    rw [hD10] at hloss
    omega

/-- Coarse editorial corollary (V3528 (0.1)): from the strong form. -/
theorem p4_133_existence_coarse
    (emap : ι → Fin 2 → Sym2 B) (Pall : Finset ι)
    (hinj : Set.InjOn (fun p : ι × Fin 2 => emap p.1 p.2) {p | p.1 ∈ Pall})
    (hloop : ∀ P ∈ Pall, ∀ i, ¬ (emap P i).IsDiag)
    (a m : ℕ) (ha1 : 1 ≤ a) (ham : a ≤ m) (X : Finset B)
    (hcover : ∀ P ∈ Pall, ∀ i, ∃ w ∈ X, w ∈ emap P i)
    (hbaseDeg : (termGraph emap Pall).maxDegree ≤ m) :
    ∃ S' : Finset ι, S' ⊆ Pall ∧
      ((termGraph emap S').lineGraph).Colorable a ∧
      a * Pall.card ≤ m * S'.card + m * (4 + 17 * X.card) := by
  classical
  obtain ⟨S', hS'sub, hcolor, hcount⟩ :=
    p4_133_existence emap Pall hinj hloop a m ha1 ham X hcover hbaseDeg
  refine ⟨S', hS'sub, hcolor, ?_⟩
  rcases Finset.eq_empty_or_nonempty Pall with rfl | ⟨P₀, hP₀⟩
  · simp
  have hm : 0 < m := lt_of_lt_of_le ha1 ham
  have hX : 1 ≤ X.card := by
    obtain ⟨w, hwX, -⟩ := hcover P₀ hP₀ 0
    exact Finset.card_pos.2 ⟨w, hwX⟩
  refine le_of_lt ?_
  calc a * Pall.card
      = m * (a * Pall.card / m) + a * Pall.card % m := (Nat.div_add_mod _ _).symm
    _ ≤ m * (S'.card + 4 + 10 * X.card) + a * Pall.card % m :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hcount) _
    _ < m * (S'.card + 4 + 10 * X.card) + m :=
        Nat.add_lt_add_left (Nat.mod_lt _ hm) _
    _ = m * (S'.card + 5 + 10 * X.card) := by ring
    _ ≤ m * (S'.card + (4 + 17 * X.card)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = m * S'.card + m * (4 + 17 * X.card) := by ring

end PaperV.TerminalPair
