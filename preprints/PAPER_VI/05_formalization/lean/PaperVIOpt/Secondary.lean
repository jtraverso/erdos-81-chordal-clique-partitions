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
Paper VI optimisation round — Priority 2: exact secondary optimisation among minimum
clique partitions, and the attainable integral block-count spectrum.

Among minimum-cardinality clique partitions (when `cp(G) = s - u - 2m`) every block is of one
of the zero-slack types `(1,1), (2,1), (2,2), (3,2)`, and every exterior edge lies in a unique
block, which is a `K_4` of type `(2,2)` or a `K_5` of type `(3,2)`. We charge an exterior edge
`e` the real amount `a e` if its block is a `K_4` and `b e` if it is a `K_5`, and charge every
block of order two `c₂` and every block of order three `c₃` (in a minimum partition these are
exactly the crossing edges and the `(2,1)` triangles). The minimum secondary cost over all
minimum partitions is
`c₂ (s - 2u - 2m) + c₃ (u - m) + Σ_{e ∈ E(H)} min(a e, b e + 2c₂ - 2c₃)`.
The lower bound only needs `cp(G) = s - u - 2m`; attainment uses Theorem B (`p ≥ 63h`).
All charges are arbitrary reals (negative values and ties allowed); `E(H) = ∅` is included.
-/
module

public import PaperVIOpt.Parametric
public import PaperVI.Optimal

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- The pair `e` lies in a block of order five of `Bs`. -/
def InK5 (Bs : Finset (Finset V)) (e : Sym2 V) : Prop :=
  ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = 5

open Classical in
/-- The secondary cost of a clique partition: `c₂` per block of order two, `c₃` per block of
order three, and for each exterior edge `e`, `b e` if `e` lies in a block of order five and
`a e` otherwise (for a minimum partition, otherwise means: in a `K_4` of type `(2,2)`). -/
noncomputable def secondaryCost (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ) (Bs : Finset (Finset V)) : ℝ :=
  c₂ * (Bs.filter (fun B => B.card = 2)).card + c₃ * (Bs.filter (fun B => B.card = 3)).card +
    ∑ e ∈ extEdges G P, (if InK5 Bs e then b e else a e)

/-- The claimed optimal secondary value
`c₂ (s - 2u - 2m) + c₃ (u - m) + Σ_e min(a e, b e + 2c₂ - 2c₃)`. -/
noncomputable def secondaryValue (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ) : ℝ :=
  c₂ * ((sCount G P : ℝ) - 2 * uCount G P - 2 * mCount G P) +
    c₃ * ((uCount G P : ℝ) - mCount G P) +
    ∑ e ∈ extEdges G P, min (a e) (b e + 2 * c₂ - 2 * c₃)

/-- For a partition realising a prescription `σ`, membership in a `K_5` is read off from `σ`. -/
theorem inK5_iff_of_prescribed {σ : Sym2 V → ℕ}
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs)
    (hpres : ∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2)
    {e : Sym2 V} (he : e ∈ extEdges G P) : InK5 Bs e ↔ σ e = 5 := by
  obtain ⟨B, hB, heB, hcard, -⟩ := hpres e he
  constructor
  · rintro ⟨B', hB', heB', hcard'⟩
    have := block_unique_of_edge G hBs (extEdges_subset he) hB hB' heB heB'
    rw [← hcard, this, hcard']
  · intro h
    exact ⟨B, hB, heB, by rw [hcard, h]⟩

/-- **Secondary cost of a prescribed partition.** -/
theorem secondaryCost_of_prescribed (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e - 2 ∧ extSize P B = 2) :
    secondaryCost G P a b c₂ c₃ Bs =
      c₂ * ((sCount G P : ℝ) - 2 * uCount G P - 2 * mCount G P) +
        c₃ * ((uCount G P : ℝ) - mCount G P) +
        ∑ e ∈ extEdges G P, (if σ e = 5 then b e + 2 * c₂ - 2 * c₃ else a e) := by
  classical
  obtain ⟨-, -, hpres, -, -, -, h3, h2⟩ := prescribed_partition_conclusions G P σ hσ hBs htypes
  set k := ((extEdges G P).filter (fun e => σ e = 5)).card with hk
  have h3R : ((Bs.filter (fun B => B.card = 3)).card : ℝ) =
      (uCount G P : ℝ) - mCount G P - 2 * k := by exact_mod_cast h3
  have h2R : ((Bs.filter (fun B => B.card = 2)).card : ℝ) =
      (sCount G P : ℝ) - 2 * uCount G P - 2 * mCount G P + 2 * k := by exact_mod_cast h2
  have hkR : (k : ℝ) = ∑ e ∈ extEdges G P, (if σ e = 5 then (1 : ℝ) else 0) := by
    rw [hk, card_filter]; push_cast; rfl
  have hsum : ∑ e ∈ extEdges G P, (if InK5 Bs e then b e else a e) =
      ∑ e ∈ extEdges G P, (if σ e = 5 then b e else a e) := by
    refine sum_congr rfl fun e he => ?_
    rw [if_congr (inK5_iff_of_prescribed G P hBs hpres he) rfl rfl]
  have hsplit : ∑ e ∈ extEdges G P, (if σ e = 5 then b e + 2 * c₂ - 2 * c₃ else a e) =
      ∑ e ∈ extEdges G P, (if σ e = 5 then b e else a e) +
        (2 * c₂ - 2 * c₃) * ∑ e ∈ extEdges G P, (if σ e = 5 then (1 : ℝ) else 0) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> ring
  unfold secondaryCost
  rw [hsum, h3R, h2R, hsplit, ← hkR]
  ring

/-- Any minimum partition has the prescribed form for the prescription read off from it. -/
theorem prescribed_of_optimal
    (hcp : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G) :
    ∃ σ : Sym2 V → ℕ, (∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) ∧
      (∀ e ∈ extEdges G P, (InK5 Bs e ↔ σ e = 5)) ∧
      ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e - 2 ∧ extSize P B = 2 := by
  classical
  have htyp := optimal_types_of_cp_eq G P hcp hBs hopt
  refine ⟨fun e => if InK5 Bs e then 5 else 4, fun e _ => by dsimp only; split_ifs <;> simp,
    fun e _ => by dsimp only; split_ifs with h <;> simp [h], fun B hB => ?_⟩
  -- blocks with two exterior vertices
  have hext : extSize P B = 2 → ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧
      (InK5 Bs e ↔ B.card = 5) := by
    intro h2
    obtain ⟨x, y, hxy, hxyB⟩ := card_eq_two.mp h2
    have hx : x ∈ B \ P := by rw [hxyB]; simp
    have hy : y ∈ B \ P := by rw [hxyB]; simp
    rw [mem_sdiff] at hx hy
    have hadj : G.Adj x y := hBs.isClique B hB hx.1 hy.1 hxy
    have he : s(x, y) ∈ extEdges G P := (mem_extEdges G P).mpr ⟨hadj, hx.2, hy.2⟩
    have heB : ∀ v ∈ s(x, y), v ∈ B := by
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hx.1
      · exact hy.1
    refine ⟨s(x, y), he, heB, ?_⟩
    constructor
    · rintro ⟨B', hB', heB', hcard'⟩
      rw [block_unique_of_edge G hBs (extEdges_subset he) hB hB' heB heB']
      exact hcard'
    · intro h5; exact ⟨B, hB, heB, h5⟩
  have hcardB := card_eq_coreSize_add_extSize P B
  rcases (htyp B hB).1 with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨e, he, heB, hiff⟩ := hext h2
    refine Or.inr (Or.inr ⟨e, he, heB, ?_, h2⟩)
    have : ¬ InK5 Bs e := fun h' => by have := hiff.mp h'; omega
    dsimp only
    rw [if_neg this, h1]
  · obtain ⟨e, he, heB, hiff⟩ := hext h2
    refine Or.inr (Or.inr ⟨e, he, heB, ?_, h2⟩)
    have : InK5 Bs e := hiff.mpr (by omega)
    dsimp only
    rw [if_pos this, h1]

/-- **Lower bound for the secondary problem.** If `cp(G) = s - u - 2m` (e.g. under Theorem A,
`p ≥ 18h + 1`), every minimum clique partition has secondary cost at least
`c₂ (s - 2u - 2m) + c₃ (u - m) + Σ_e min(a e, b e + 2c₂ - 2c₃)`. -/
theorem secondaryValue_le_cost (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ)
    (hcp : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G) :
    secondaryValue G P a b c₂ c₃ ≤ secondaryCost G P a b c₂ c₃ Bs := by
  obtain ⟨σ, hσ, -, htypes⟩ := prescribed_of_optimal G P hcp hBs hopt
  rw [secondaryCost_of_prescribed G P a b c₂ c₃ σ hσ hBs htypes]
  unfold secondaryValue
  have : ∑ e ∈ extEdges G P, min (a e) (b e + 2 * c₂ - 2 * c₃) ≤
      ∑ e ∈ extEdges G P, (if σ e = 5 then b e + 2 * c₂ - 2 * c₃ else a e) := by
    refine sum_le_sum fun e _ => ?_
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _
  linarith

/-- **Attainment.** Under the hypotheses of Theorem B (`n ≥ 2`, `p = ⌊(n+1)/3⌋`, `p ≥ 63h`),
some minimum clique partition has secondary cost exactly
`c₂ (s - 2u - 2m) + c₃ (u - m) + Σ_e min(a e, b e + 2c₂ - 2c₃)`: prescribe `K_5` exactly on the
exterior edges with `b e + 2c₂ - 2c₃ < a e`. -/
theorem exists_secondary_optimal (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      secondaryCost G P a b c₂ c₃ Bs = secondaryValue G P a b c₂ c₃ := by
  classical
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  have hpq : P.card ≤ Pᶜ.card := by rw [hq, hP]; exact p_le_q _
  let σ : Sym2 V → ℕ := fun e => if b e + 2 * c₂ - 2 * c₃ < a e then 5 else 4
  have hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5 := fun e _ => by
    simp only [σ]; split_ifs <;> simp
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_B G P hq1 hq0 hpq hh σ hσ
  obtain ⟨hcard, -⟩ := prescribed_partition_conclusions G P σ hσ hBs htypes
  refine ⟨Bs, hBs, hcard, ?_⟩
  rw [secondaryCost_of_prescribed G P a b c₂ c₃ σ hσ hBs htypes]
  unfold secondaryValue
  congr 1
  refine sum_congr rfl fun e _ => ?_
  by_cases h1 : b e + 2 * c₂ - 2 * c₃ < a e
  · simp only [σ, if_pos h1, if_true]
    exact (min_eq_right h1.le).symm
  · simp only [σ, if_neg h1, show (4 : ℕ) ≠ 5 by norm_num, if_false]
    exact (min_eq_left (not_lt.mp h1)).symm

/-- **Exact secondary optimum.** Under the hypotheses of Theorem B, the minimum secondary cost
over all minimum clique partitions equals
`c₂ (s - 2u - 2m) + c₃ (u - m) + Σ_e min(a e, b e + 2c₂ - 2c₃)`. -/
theorem secondary_optimum (a b : Sym2 V → ℝ) (c₂ c₃ : ℝ) (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card) :
    IsLeast {v : ℝ | ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      secondaryCost G P a b c₂ c₃ Bs = v} (secondaryValue G P a b c₂ c₃) := by
  have hcp : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P := by
    obtain ⟨-, -, -, h, -⟩ := theoremB G P hn hP hh (fun _ => 4) (fun _ _ => Or.inl rfl)
    exact h
  obtain ⟨Bs, hBs, hcard, hval⟩ := exists_secondary_optimal G P a b c₂ c₃ hP hh
  refine ⟨⟨Bs, hBs, hcard, hval⟩, ?_⟩
  rintro v ⟨Bs', hBs', hcard', rfl⟩
  exact secondaryValue_le_cost G P a b c₂ c₃ hcp hBs' hcard'

/-! ### The attainable integral block-count spectrum -/

/-- **Block counts of every minimum partition.** If `cp(G) = s - u - 2m`, every minimum
clique partition has block orders in `{2,3,4,5}` and, for some `0 ≤ k ≤ m`,
`(N₅, N₄, N₃, N₂) = (k, m - k, u - m - 2k, s - 2u - 2m + 2k)`. -/
theorem optimal_block_counts
    (hcp : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P)
    {Bs : Finset (Finset V)} (hBs : IsCliquePartition G Bs) (hopt : Bs.card = cp G) :
    ∃ k : ℕ, k ≤ mCount G P ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) = k ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) = (mCount G P : ℤ) - k ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) = (uCount G P : ℤ) - mCount G P - 2 * k ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P + 2 * k := by
  obtain ⟨σ, hσ, -, htypes⟩ := prescribed_of_optimal G P hcp hBs hopt
  obtain ⟨-, -, -, -, h5, h4, h3, h2⟩ := prescribed_partition_conclusions G P σ hσ hBs htypes
  exact ⟨_, card_filter_le _ _, h5, h4, h3, h2⟩

/-- **Every value of `N₅` is attained.** Under the hypotheses of Theorem B, for every
`0 ≤ k ≤ m` there is a minimum clique partition with
`(N₅, N₄, N₃, N₂) = (k, m - k, u - m - 2k, s - 2u - 2m + 2k)`. Together with
`optimal_block_counts`, these are exactly the block-count vectors of minimum partitions. -/
theorem exists_optimal_block_counts (hn : 2 ≤ Fintype.card V)
    (hP : P.card = (Fintype.card V + 1) / 3) (hh : 63 * editDegree G P ≤ P.card)
    (k : ℕ) (hk : k ≤ mCount G P) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) = k ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) = (mCount G P : ℤ) - k ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) = (uCount G P : ℤ) - mCount G P - 2 * k ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P + 2 * k := by
  classical
  obtain ⟨S, hS, hSk⟩ := exists_subset_card_eq (s := extEdges G P) hk
  let σ : Sym2 V → ℕ := fun e => if e ∈ S then 5 else 4
  have hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5 := fun e _ => by
    simp only [σ]; split_ifs <;> simp
  have hfil : (extEdges G P).filter (fun e => σ e = 5) = S := by
    ext e
    simp only [mem_filter, σ]
    constructor
    · intro hh'
      by_contra h'
      simp [h'] at hh'
    · intro h; exact ⟨hS h, by simp [h]⟩
  obtain ⟨Bs, hBs, hcard, -, -, -, -, h5, h4, h3, h2⟩ := theoremB G P hn hP hh σ hσ
  rw [hfil, hSk] at h5 h4 h3 h2
  exact ⟨Bs, hBs, hcard, h5, h4, h3, h2⟩

end PaperVI
