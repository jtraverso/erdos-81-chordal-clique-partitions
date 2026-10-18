/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — Section 2.2 (available cliques in a set with a bounded forbidden-pair graph) and
the finite induction constructing exterior-edge lifts with bounded vertex load
(Sections 3, 4 and 5, first stage).
-/
module

public import PaperVI.Local

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Section 2.2, in general form: if every vertex of `K` has at most `D` forbidden partners
in `K` and `k (D+1) ≤ |K| + D` (i.e. `|K| ≥ (k-1)(D+1)+1` for `k ≥ 1`), then `K` contains `k`
vertices with no forbidden pair. For `k = 2` this is `|K| ≥ D + 2`, for `k = 3` it is
`|K| ≥ 2D + 3`. -/
theorem exists_good_clique (bad : V → V → Prop) [DecidableRel bad]
    (hsymm : ∀ a b, bad a b → bad b a) (D : ℕ) :
    ∀ (k : ℕ) (K : Finset V), (∀ a ∈ K, ((K.erase a).filter (bad a)).card ≤ D) →
      k * (D + 1) ≤ K.card + D →
      ∃ N ⊆ K, N.card = k ∧ ∀ a ∈ N, ∀ b ∈ N, a ≠ b → ¬ bad a b
  | 0, K, _, _ => ⟨∅, empty_subset _, rfl, by simp⟩
  | k + 1, K, hD, hk => by
    have hpos : 0 < K.card := by
      have : (k + 1) * (D + 1) = k * (D + 1) + D + 1 := by ring
      omega
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    set K' := (K.erase a).filter (fun b => ¬ bad a b) with hK'
    have hK'sub : K' ⊆ K := (filter_subset _ _).trans (erase_subset _ _)
    have hK'card : K.card ≤ K'.card + D + 1 := by
      have h1 : ((K.erase a).filter (bad a)).card + K'.card = (K.erase a).card := by
        rw [hK']; convert card_filter_add_card_filter_not (s := K.erase a) (bad a)
      have h2 := card_erase_of_mem ha
      have h3 := hD a ha
      omega
    have hD' : ∀ b ∈ K', ((K'.erase b).filter (bad b)).card ≤ D := fun b hb =>
      le_trans (card_le_card (filter_subset_filter _ (erase_subset_erase _ hK'sub)))
        (hD b (hK'sub hb))
    have hk' : k * (D + 1) ≤ K'.card + D := by
      have : (k + 1) * (D + 1) = k * (D + 1) + D + 1 := by ring
      omega
    obtain ⟨N', hN'K, hN'c, hN'good⟩ := exists_good_clique bad hsymm D k K' hD' hk'
    have haN' : a ∉ N' := fun h => by
      have := hN'K h
      simp [hK'] at this
    refine ⟨insert a N', insert_subset ha (hN'K.trans hK'sub), by rw [card_insert_of_notMem haN',
      hN'c], ?_⟩
    intro u hu v hv huv
    rw [mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl huv
    · have := hN'K hv; simp only [hK', mem_filter] at this; exact this.2
    · have := hN'K hu; simp only [hK', mem_filter] at this; exact fun h => this.2 (hsymm _ _ h)
    · exact hN'good u hu v hv huv

/-- The invariant of the lifting induction, for a set `D` of processed exterior edges and the
core sets `T e` assigned to them: core sets lie in `P` and have the prescribed size, all block
edges are present, core pairs are never reused, the core sets of incident exterior edges are
disjoint, and every core vertex has load at most `r`. -/
structure LiftInv (G : SimpleGraph V) (P : Finset V) (σ : Sym2 V → ℕ) (r : ℕ)
    (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) : Prop where
  sub : ∀ e ∈ D, T e ⊆ P
  card : ∀ e ∈ D, (T e).card = σ e
  coreAdj : ∀ e ∈ D, ∀ a ∈ T e, ∀ b ∈ T e, a ≠ b → G.Adj a b
  crossAdj : ∀ e ∈ D, ∀ a ∈ T e, ∀ x ∈ e, G.Adj a x
  pairDisj : ∀ e ∈ D, ∀ e' ∈ D, e ≠ e' → ∀ a ∈ T e, ∀ b ∈ T e, a ≠ b → a ∈ T e' → b ∉ T e'
  incDisj : ∀ e ∈ D, ∀ e' ∈ D, e ≠ e' → ∀ x ∈ e, x ∈ e' → ∀ a ∈ T e, a ∉ T e'
  load : ∀ a, (D.filter (fun e => a ∈ T e)).card ≤ r

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The total load is `Σ_e |T e|`. -/
theorem sum_load (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) :
    ∑ a, (D.filter (fun e => a ∈ T e)).card = ∑ e ∈ D, (T e).card := by
  rw [sum_card_filter_comm]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  ext a
  simp

/-- The candidate set before processing the exterior edge `xy`. -/
def candidates (r : ℕ) (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) (x y : V) : Finset V :=
  P.filter (fun a => G.Adj x a ∧ G.Adj y a ∧ (∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e) ∧
    (D.filter (fun e => a ∈ T e)).card < r)

/-- The forbidden-pair relation: missing core edges and core pairs already used. -/
def forbidden (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) (a b : V) : Prop :=
  ¬ G.Adj a b ∨ ∃ e ∈ D, a ∈ T e ∧ b ∈ T e

instance (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) : DecidableRel (forbidden G D T) :=
  fun a b => by unfold forbidden; infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem forbidden_symm (D : Finset (Sym2 V)) (T : Sym2 V → Finset V) (a b : V)
    (h : forbidden G D T a b) : forbidden G D T b a := by
  rcases h with h | ⟨e, he, ha, hb⟩
  · exact Or.inl (fun h' => h h'.symm)
  · exact Or.inr ⟨e, he, hb, ha⟩

/-- Bound on the number of candidates (estimates (14)–(15) and (19), before arithmetic). -/
theorem candidates_count {σ : Sym2 V → ℕ} {c r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T) (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hD : D ⊆ extEdges G P) {x y : V} (he0 : s(x, y) ∈ extEdges G P) (he0D : s(x, y) ∉ D) :
    ∃ bx by_ dx dy sat : ℕ,
      P.card ≤ (candidates G P r D T x y).card + bx + by_ + c * dx + c * dy + sat ∧
      bx + dx + 1 ≤ editDegree G P ∧ by_ + dy + 1 ≤ editDegree G P ∧
      r * sat ≤ c * D.card ∧ D.card + 1 ≤ mCount G P := by
  rw [mem_extEdges] at he0
  obtain ⟨hxy, hx, hy⟩ := he0
  refine ⟨(P.filter (fun a => ¬ G.Adj x a)).card, (P.filter (fun a => ¬ G.Adj y a)).card,
    (D.filter (fun e => x ∈ e)).card, (D.filter (fun e => y ∈ e)).card,
    (P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card)).card, ?_, ?_, ?_, ?_, ?_⟩
  · -- covering of `P`
    have hcov : P ⊆ candidates G P r D T x y ∪ P.filter (fun a => ¬ G.Adj x a) ∪
        P.filter (fun a => ¬ G.Adj y a) ∪ (D.filter (fun e => x ∈ e)).biUnion T ∪
        (D.filter (fun e => y ∈ e)).biUnion T ∪
        P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card) := by
      intro a ha
      by_cases h1 : G.Adj x a
      · by_cases h2 : G.Adj y a
        · by_cases h3 : ∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e
          · by_cases h4 : (D.filter (fun e => a ∈ T e)).card < r
            · simp only [mem_union]
              left; left; left; left; left
              simp only [candidates, mem_filter]
              exact ⟨ha, h1, h2, h3, h4⟩
            · simp only [mem_union]; right
              simp only [mem_filter]; exact ⟨ha, by omega⟩
          · push_neg at h3
            obtain ⟨e, he, hxy', hae⟩ := h3
            rcases hxy' with hxe | hye
            · simp only [mem_union]; left; left; right
              simp only [mem_biUnion, mem_filter]; exact ⟨e, ⟨he, hxe⟩, hae⟩
            · simp only [mem_union]; left; right
              simp only [mem_biUnion, mem_filter]; exact ⟨e, ⟨he, hye⟩, hae⟩
        · simp only [mem_union]; left; left; left; right
          simp only [mem_filter]; exact ⟨ha, h2⟩
      · simp only [mem_union]; left; left; left; left; right
        simp only [mem_filter]; exact ⟨ha, h1⟩
    have hU : ∀ Dz ⊆ D, (Dz.biUnion T).card ≤ c * Dz.card := by
      intro Dz hDz
      refine (card_biUnion_le).trans ?_
      calc ∑ e ∈ Dz, (T e).card ≤ ∑ _e ∈ Dz, c :=
            sum_le_sum fun e he => (hinv.card e (hDz he)).symm ▸ hσc e (hD (hDz he))
        _ = c * Dz.card := by rw [sum_const, smul_eq_mul, mul_comm]
    refine (card_le_card hcov).trans ?_
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (card_union_le _ _).trans (add_le_add ?_ (hU _ (filter_subset _ _)))
    refine (card_union_le _ _).trans (add_le_add ?_ (hU _ (filter_subset _ _)))
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_union_le _ _
  · have hsub : insert s(x, y) (D.filter (fun e => x ∈ e)) ⊆
        (extEdges G P).filter (fun e => x ∈ e) := by
      intro e he
      rw [mem_insert] at he
      rcases he with rfl | he
      · simp only [mem_filter, mem_extEdges, Sym2.mem_iff, true_or, and_true]
        exact ⟨hxy, hx, hy⟩
      · simp only [mem_filter] at he ⊢; exact ⟨hD he.1, he.2⟩
    have hnot : s(x, y) ∉ D.filter (fun e => x ∈ e) := fun h => he0D (mem_filter.mp h).1
    have h1 : (D.filter (fun e => x ∈ e)).card + 1 ≤
        ((extEdges G P).filter (fun e => x ∈ e)).card := by
      have := card_le_card hsub
      rwa [card_insert_of_notMem hnot] at this
    have h2 := card_extEdges_incident_le G P x
    have h3 := ext_local_bound G P x hx
    omega
  · have hsub : insert s(x, y) (D.filter (fun e => y ∈ e)) ⊆
        (extEdges G P).filter (fun e => y ∈ e) := by
      intro e he
      rw [mem_insert] at he
      rcases he with rfl | he
      · simp only [mem_filter, mem_extEdges, Sym2.mem_iff, or_true, and_true]
        exact ⟨hxy, hx, hy⟩
      · simp only [mem_filter] at he ⊢; exact ⟨hD he.1, he.2⟩
    have hnot : s(x, y) ∉ D.filter (fun e => y ∈ e) := fun h => he0D (mem_filter.mp h).1
    have h1 : (D.filter (fun e => y ∈ e)).card + 1 ≤
        ((extEdges G P).filter (fun e => y ∈ e)).card := by
      have := card_le_card hsub
      rwa [card_insert_of_notMem hnot] at this
    have h2 := card_extEdges_incident_le G P y
    have h3 := ext_local_bound G P y hy
    omega
  · calc r * (P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card)).card
        = ∑ _a ∈ P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card), r := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ P.filter (fun a => r ≤ (D.filter (fun e => a ∈ T e)).card),
            (D.filter (fun e => a ∈ T e)).card :=
          sum_le_sum fun a ha => (mem_filter.mp ha).2
      _ ≤ ∑ a, (D.filter (fun e => a ∈ T e)).card :=
          sum_le_sum_of_subset (subset_univ _)
      _ = ∑ e ∈ D, (T e).card := sum_load D T
      _ ≤ ∑ _e ∈ D, c := sum_le_sum fun e he => (hinv.card e he).symm ▸ hσc e (hD he)
      _ = c * D.card := by rw [sum_const, smul_eq_mul, mul_comm]
  · have hmem : s(x, y) ∈ extEdges G P := by rw [mem_extEdges]; exact ⟨hxy, hx, hy⟩
    have : D ⊂ extEdges G P :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hD, fun h => he0D (h ▸ hmem)⟩
    exact card_lt_card this

/-- Bound on the forbidden degree inside the candidate set: at most `h + (c-1) r`. -/
theorem forbidden_degree {σ : Sym2 V → ℕ} {c r : ℕ} {D : Finset (Sym2 V)}
    {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T) (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hD : D ⊆ extEdges G P) (K : Finset V) (hK : K ⊆ P) :
    ∀ a ∈ K, ((K.erase a).filter (forbidden G D T a)).card ≤
      editDegree G P + (c - 1) * r := by
  intro a ha
  have haP := hK ha
  have hsub : (K.erase a).filter (forbidden G D T a) ⊆
      P.filter (fun b => b ≠ a ∧ ¬ G.Adj a b) ∪
        (D.filter (fun e => a ∈ T e)).biUnion (fun e => (T e).erase a) := by
    intro b hb
    simp only [mem_filter, mem_erase] at hb
    obtain ⟨⟨hba, hbK⟩, hf⟩ := hb
    rcases hf with hf | ⟨e, he, hae, hbe⟩
    · exact mem_union_left _ (mem_filter.mpr ⟨hK hbK, hba, hf⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hae⟩,
        mem_erase.mpr ⟨hba, hbe⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := core_local_bound G P a haP
  have h2 : ((D.filter (fun e => a ∈ T e)).biUnion (fun e => (T e).erase a)).card ≤
      (c - 1) * r := by
    refine card_biUnion_le.trans ?_
    calc ∑ e ∈ D.filter (fun e => a ∈ T e), ((T e).erase a).card
        ≤ ∑ _e ∈ D.filter (fun e => a ∈ T e), (c - 1) := by
          refine sum_le_sum fun e he => ?_
          rw [mem_filter] at he
          rw [card_erase_of_mem he.2, hinv.card e he.1]
          have := hσc e (hD he.1)
          omega
      _ = (c - 1) * (D.filter (fun e => a ∈ T e)).card := by
          rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ (c - 1) * r := Nat.mul_le_mul_left _ (hinv.load a)
  omega

/-- One step of the lifting induction: process the exterior edge `xy`. -/
theorem lift_step {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k)
    {D : Finset (Sym2 V)} {T : Sym2 V → Finset V} (hinv : LiftInv G P σ r D T)
    (hD : D ⊆ extEdges G P) {e0 : Sym2 V} (he0 : e0 ∈ extEdges G P) (he0D : e0 ∉ D) :
    ∃ T', LiftInv G P σ r (insert e0 D) T' := by
  induction e0 using Sym2.ind with
  | h x y =>
  obtain ⟨bx, by_, dx, dy, sat, h1, h2, h3, h4, h5⟩ :=
    candidates_count G P hinv hσc hD he0 he0D
  have hK := hcand _ _ _ _ _ _ _ h1 h2 h3 h4 h5 (two_mCount_le G P)
  set K := candidates G P r D T x y with hKdef
  have hKP : K ⊆ P := filter_subset _ _
  have hdeg := forbidden_degree G P hinv hσc hD K hKP
  have hk : σ s(x, y) * (editDegree G P + (c - 1) * r + 1) ≤
      K.card + (editDegree G P + (c - 1) * r) := (hneed _ he0).trans (by omega)
  obtain ⟨N, hNK, hNc, hNgood⟩ := exists_good_clique (forbidden G D T) (forbidden_symm G D T)
    _ _ K hdeg hk
  have hNmem : ∀ a ∈ N, a ∈ P ∧ G.Adj x a ∧ G.Adj y a ∧
      (∀ e ∈ D, (x ∈ e ∨ y ∈ e) → a ∉ T e) ∧ (D.filter (fun e => a ∈ T e)).card < r := by
    intro a ha
    have := hNK ha
    simp only [hKdef, candidates, mem_filter] at this
    exact this
  have hNgood' : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → G.Adj a b ∧ ∀ e ∈ D, a ∈ T e → b ∉ T e := by
    intro a ha b hb hab
    have := hNgood a ha b hb hab
    simp only [forbidden, not_or, not_not, not_exists, not_and] at this
    exact ⟨this.1, this.2⟩
  let T' : Sym2 V → Finset V := fun e => if e = s(x, y) then N else T e
  have hT'0 : T' s(x, y) = N := by simp [T']
  have hT'D : ∀ e ∈ D, T' e = T e := fun e he => by
    have : e ≠ s(x, y) := fun h => he0D (h ▸ he)
    simp [T', this]
  have hne : ∀ e ∈ D, e ≠ s(x, y) := fun e he h => he0D (h ▸ he)
  refine ⟨T', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e he
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0]; exact hNK.trans hKP
    · rw [hT'D e he]; exact hinv.sub e he
  · intro e he
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0, hNc]
    · rw [hT'D e he]; exact hinv.card e he
  · intro e he a ha b hb hab
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at ha hb; exact (hNgood' a ha b hb hab).1
    · rw [hT'D e he] at ha hb; exact hinv.coreAdj e he a ha b hb hab
  · intro e he a ha z hz
    rw [mem_insert] at he
    rcases he with rfl | he
    · rw [hT'0] at ha
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact (hNmem a ha).2.1.symm
      · exact (hNmem a ha).2.2.1.symm
    · rw [hT'D e he] at ha; exact hinv.crossAdj e he a ha z hz
  · intro e he e' he' hee' a ha b hb hab hae'
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at ha hb; rw [hT'D e' he'] at hae' ⊢
      exact (hNgood' a ha b hb hab).2 e' he' hae'
    · rw [hT'D e he] at ha hb; rw [hT'0] at hae' ⊢
      intro hbN
      exact (hNgood' a hae' b hbN hab).2 e he ha hb
    · rw [hT'D e he] at ha hb; rw [hT'D e' he'] at hae' ⊢
      exact hinv.pairDisj e he e' he' hee' a ha b hb hab hae'
  · intro e he e' he' hee' z hz hz' a ha
    rw [mem_insert] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hee'
    · rw [hT'0] at ha; rw [hT'D e' he']
      refine (hNmem a ha).2.2.2.1 e' he' ?_
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hz'
      · exact Or.inr hz'
    · rw [hT'D e he] at ha; rw [hT'0]
      intro haN
      refine (hNmem a haN).2.2.2.1 e he ?_ ha
      rw [Sym2.mem_iff] at hz'
      rcases hz' with rfl | rfl
      · exact Or.inl hz
      · exact Or.inr hz
    · rw [hT'D e he] at ha; rw [hT'D e' he']
      exact hinv.incDisj e he e' he' hee' z hz hz' a ha
  · intro a
    have hfD : D.filter (fun e => a ∈ T' e) = D.filter (fun e => a ∈ T e) :=
      filter_congr fun e he => by rw [hT'D e he]
    rw [filter_insert, hT'0]
    split_ifs with haN
    · rw [card_insert_of_notMem (fun h => he0D (mem_filter.mp h).1), hfD]
      have := (hNmem a haN).2.2.2.2
      omega
    · rw [hfD]; exact hinv.load a

/-- **The lifting lemma.** Under the counting hypothesis `hcand` and the size condition
`hneed`, every exterior edge `e` receives a core set `T e` of size `σ e` such that the lifting
invariant holds for all exterior edges with maximum load `r`. -/
theorem exists_lift {σ : Sym2 V → ℕ} {c r need : ℕ}
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcand : ∀ k bx by_ dx dy sat nD : ℕ, P.card ≤ k + bx + by_ + c * dx + c * dy + sat →
      bx + dx + 1 ≤ editDegree G P → by_ + dy + 1 ≤ editDegree G P → r * sat ≤ c * nD →
      nD + 1 ≤ mCount G P → 2 * mCount G P ≤ Pᶜ.card * editDegree G P → need ≤ k) :
    ∃ T, LiftInv G P σ r (extEdges G P) T := by
  refine Finset.induction_on' (motive := fun D => ∃ T, LiftInv G P σ r D T) (extEdges G P)
    ⟨fun _ => ∅, by constructor <;> simp⟩ ?_
  intro e0 D he0 hD he0D ih
  obtain ⟨T, hT⟩ := ih
  exact lift_step G P hσc hneed hcand hT hD he0 he0D

end PaperVI
