/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI optimisation round — Priority 3: an explicit parametric construction theorem.

The slack certificate `cp(G) ≥ s - u - 2m` holds for every bipartition. The construction
of the baseline (`exists_partition_of_lift`) is stated with an abstract counting hypothesis.
Here that hypothesis is replaced by explicit inequalities in `p = |P|`, `q = |O|`, the
modification parameter `h`, the actual number `m` of exterior edges, and an auxiliary load
cap `r`.  No relation between `p` and `n` (such as `p = ⌊(n+1)/3⌋`) is assumed.
-/
module

public import PaperVI.TheoremB

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)

/-- `s - u - 2m = pq - binom(p,2) + C - A - 2m` with `q = n - p`, for every bipartition. -/
theorem sum_formula_pq :
    (sCount G P : ℤ) - uCount G P - 2 * mCount G P =
      (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) + Cdef G P -
        Adef G P - 2 * mCount G P := by
  unfold Cdef Adef; ring

/-- **Explicit lifting capacity.** The abstract counting hypothesis of
`exists_partition_of_lift` follows from the explicit capacity inequality
`r (need + 2c(h-1)) + c(m-1) ≤ r p` (required only when `h ≥ 1` and `m ≥ 1`) together with
`c ≥ 1` and `r ≥ 1`. -/
theorem exists_partition_param {σ : Sym2 V → ℕ} {c r need : ℕ} (hc : 1 ≤ c)
    (hσc : ∀ e ∈ extEdges G P, σ e ≤ c)
    (hneed : ∀ e ∈ extEdges G P, σ e * (editDegree G P + (c - 1) * r + 1) ≤
      need + (editDegree G P + (c - 1) * r))
    (hcap : 1 ≤ editDegree G P → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * (need + 2 * c * ((editDegree G P : ℤ) - 1)) + c * ((mCount G P : ℤ) - 1) ≤
        r * P.card)
    (hlist : P.card + 2 * (editDegree G P + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ ∀ B ∈ Bs,
      (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  refine exists_partition_of_lift G P hσc hneed ?_ hlist
  intro k bx by_ dx dy sat nD h1 h2 h3 h4 h5 _h6
  obtain ⟨hr, hineq⟩ := hcap (by omega) (by omega)
  have hbx : bx + c * dx ≤ c * (editDegree G P - 1) := by
    have : bx + dx ≤ editDegree G P - 1 := by omega
    calc bx + c * dx ≤ c * bx + c * dx := by nlinarith
      _ = c * (bx + dx) := by ring
      _ ≤ c * (editDegree G P - 1) := Nat.mul_le_mul_left _ this
  have hby : by_ + c * dy ≤ c * (editDegree G P - 1) := by
    have : by_ + dy ≤ editDegree G P - 1 := by omega
    calc by_ + c * dy ≤ c * by_ + c * dy := by nlinarith
      _ = c * (by_ + dy) := by ring
      _ ≤ c * (editDegree G P - 1) := Nat.mul_le_mul_left _ this
  have hsat : r * sat ≤ c * (mCount G P - 1) :=
    h4.trans (Nat.mul_le_mul_left _ (by omega))
  have hh1 : 1 ≤ editDegree G P := by omega
  have hm1 : 1 ≤ mCount G P := by omega
  have e1 : ((editDegree G P - 1 : ℕ) : ℤ) = (editDegree G P : ℤ) - 1 := by push_cast [hh1]; ring
  have e2 : ((mCount G P - 1 : ℕ) : ℤ) = (mCount G P : ℤ) - 1 := by push_cast [hm1]; ring
  have hbxZ : (bx : ℤ) + c * dx ≤ c * ((editDegree G P : ℤ) - 1) := by
    rw [← e1]; exact_mod_cast hbx
  have hbyZ : (by_ : ℤ) + c * dy ≤ c * ((editDegree G P : ℤ) - 1) := by
    rw [← e1]; exact_mod_cast hby
  have hsatZ : (r : ℤ) * sat ≤ c * ((mCount G P : ℤ) - 1) := by
    rw [← e2]; exact_mod_cast hsat
  have h1Z : (P.card : ℤ) ≤ k + bx + by_ + c * dx + c * dy + sat := by exact_mod_cast h1
  have hrZ : (0 : ℤ) < r := by exact_mod_cast hr
  have key : (r : ℤ) * need ≤ r * k := by nlinarith
  exact_mod_cast le_of_mul_le_mul_left key hrZ


/-! ### Theorem A, parametric form -/

/-- **Parametric Theorem A.** Let `p = |P|`, `q = |O|`, `h`, `m` be arbitrary (no relation to
`n = |V|` is assumed) and let `r` be an auxiliary load cap. If
`p + 2(h + 2r) ≤ q` (completion capacity) and, when `h, m ≥ 1`, `r ≥ 1` and
`r (5h + r - 2) + 2(m - 1) ≤ r p` (lifting capacity, with the actual `m`), then
`cp(G) = cp_{≤4}(G) = s - u - 2m = pq - binom(p,2) + C - A - 2m`, attained by a partition with
`m` blocks `K_4` of type `(2,2)`, `u - m` triangles `(2,1)` and `s - 2u - 2m` crossing edges. -/
theorem cp_param_K4 (r : ℕ)
    (hcap : 1 ≤ editDegree G P → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * (5 * (editDegree G P : ℤ) + r - 2) + 2 * ((mCount G P : ℤ) - 1) ≤ r * P.card)
    (hlist : P.card + 2 * (editDegree G P + 2 * r) ≤ Pᶜ.card) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
      Cdef G P - Adef G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ B ∈ Bs, B.card ≤ 4) ∧ (∀ B ∈ Bs, IsTypeA P B) ∧
      typeCount P Bs 2 2 = mCount G P ∧
      (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
      (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_param G P (σ := fun _ => 2) (c := 2) (r := r)
    (need := editDegree G P + r + 2) (by norm_num) (fun _ _ => le_rfl)
    (fun _ _ => by simp only [Nat.add_one_sub_one, one_mul]; omega)
    (fun h1 h2 => by
      obtain ⟨hr, hc⟩ := hcap h1 h2
      refine ⟨hr, ?_⟩
      push_cast
      linarith)
    hlist
  have htA : ∀ B ∈ Bs, IsTypeA P B := fun B hB => by
    rcases htypes B hB with h | h | ⟨e, -, -, hc, hb⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨hc, hb⟩
  obtain ⟨hcp, h4, hcard, hle, c22, c21, c11⟩ := theoremA_conclusions G P hBs htA
  exact ⟨hcp, hcp.trans (sum_formula_pq G P), h4, Bs, hBs, hcard, hle, htA, c22, c21, c11⟩

/-- **Wide-ratio Theorem A.** For every integer `t ≥ 1`, if
`p + (4t+2) h ≤ q` and `q h ≤ t h (p - (t+5) h + 2) + 2`, then `cp(G) = s - u - 2m`
(with the same optimal `K_4`/triangle/edge structure). In particular this holds whenever
`p + (4t+2)h ≤ q ≤ t (p - (t+5) h)`. No relation between `p` and `n` is assumed: e.g. `t = 4`
covers `p + 18h ≤ q ≤ 4p - 36h`. The load cap used is `r = t h`. -/
theorem cp_window_K4 (t : ℕ) (ht : 1 ≤ t)
    (hlow : P.card + (4 * t + 2) * editDegree G P ≤ Pᶜ.card)
    (hup : (Pᶜ.card : ℤ) * editDegree G P ≤
      t * editDegree G P * ((P.card : ℤ) - (t + 5) * editDegree G P + 2) + 2) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
      Cdef G P - Adef G P - 2 * mCount G P ∧
    cp G = cpLe 4 G ∧
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (∀ B ∈ Bs, B.card ≤ 4) ∧ (∀ B ∈ Bs, IsTypeA P B) ∧
      typeCount P Bs 2 2 = mCount G P ∧
      (typeCount P Bs 2 1 : ℤ) = (uCount G P : ℤ) - mCount G P ∧
      (typeCount P Bs 1 1 : ℤ) = (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P := by
  refine cp_param_K4 G P (t * editDegree G P) (fun h1 _ => ⟨Nat.mul_pos ht h1, ?_⟩) ?_
  · have hm := two_mCount_le G P
    have hmZ : 2 * (mCount G P : ℤ) ≤ Pᶜ.card * editDegree G P := by exact_mod_cast hm
    push_cast
    nlinarith
  · nlinarith

/-- **Wide-ratio Theorem A, simplified window.** For every integer `t ≥ 1`, if
`p + (4t+2) h ≤ q` and `q + t (t+5) h ≤ t p`, then `cp(G) = s - u - 2m`
`= pq - binom(p,2) + C - A - 2m`. Consequently, for every fixed ratio `q/p = ρ > 1`, choosing an
integer `t > ρ`, the formula holds once `p ≥ max((4t+2)h/(ρ-1), t(t+5)h/(t-ρ))`. -/
theorem cp_window_K4_simple (t : ℕ) (ht : 1 ≤ t)
    (hlow : P.card + (4 * t + 2) * editDegree G P ≤ Pᶜ.card)
    (hup : Pᶜ.card + t * (t + 5) * editDegree G P ≤ t * P.card) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
      Cdef G P - Adef G P - 2 * mCount G P := by
  have hupZ : (Pᶜ.card : ℤ) + t * (t + 5) * editDegree G P ≤ t * P.card := by exact_mod_cast hup
  have h0 : (0 : ℤ) ≤ editDegree G P := by positivity
  obtain ⟨h1, h2, -⟩ := cp_window_K4 G P t ht hlow (by nlinarith)
  exact ⟨h1, h2⟩

/-- **Sparse exterior perturbations (load cap `r = 1`).** If `p + 2h + 4 ≤ q` and
`2m + 5h ≤ p + 3`, then `cp(G) = s - u - 2m`. Only the actual number `m` of exterior edges
enters, not the bound `m ≤ qh/2`; `q` may be arbitrarily large compared with `p`. -/
theorem cp_sparse_K4 (hq : P.card + 2 * editDegree G P + 4 ≤ Pᶜ.card)
    (hm : 2 * mCount G P + 5 * editDegree G P ≤ P.card + 3) :
    (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
    (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
      Cdef G P - Adef G P - 2 * mCount G P := by
  obtain ⟨h1, h2, -⟩ := cp_param_K4 G P 1 (fun _ _ => ⟨one_pos, by push_cast; omega⟩)
    (by omega)
  exact ⟨h1, h2⟩

/-- **Theorem A recovered from the wide-ratio theorem** (window `t = 4`), in the manuscript
setting `p = ⌊(n+1)/3⌋`, `p ≥ 18h + 1`. -/
theorem theoremA_from_window (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 18 * editDegree G P + 1 ≤ P.card) :
    (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  have hup : (Pᶜ.card : ℤ) * editDegree G P ≤
      ((4 : ℕ) : ℤ) * editDegree G P * ((P.card : ℤ) - ((4 : ℕ) + 5) * editDegree G P + 2) + 2 := by
    have : (Pᶜ.card : ℤ) ≤ 2 * P.card + 1 := by exact_mod_cast hq1
    have hhZ : 18 * (editDegree G P : ℤ) + 1 ≤ P.card := by exact_mod_cast hh
    have h0 : (0 : ℤ) ≤ editDegree G P := by positivity
    push_cast
    nlinarith
  obtain ⟨-, hcp, -⟩ := cp_window_K4 G P 4 (by norm_num) (by omega) hup
  have hM := Mval_eq (Fintype.card V)
  rw [← hP] at hM
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  rw [hcp, hM]
  push_cast [hpn]
  ring

/-! ### Theorem B, parametric form -/

/-- Conclusions of the prescribed-block construction without any assumption relating `p` and
`n` (the baseline `theoremB_of_partition` with its `M(n)` clause removed). -/
theorem prescribed_partition_conclusions (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) {Bs : Finset (Finset V)}
    (hBs : IsCliquePartition G Bs)
    (htypes : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e - 2 ∧ extSize P B = 2) :
    Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  -- block types and zero slack
  have htypes4 : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) ∨ (coreSize P B = 1 ∧ extSize P B = 2) := by
    intro B hB
    rcases htypes B hB with h | h | ⟨e, he, -, hc, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hσ e he with h | h <;> rw [h] at hc
      · exact Or.inr (Or.inr (Or.inl ⟨hc, hb⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc, hb⟩)))
  have htypesB : ∀ B ∈ Bs, (coreSize P B = 1 ∧ extSize P B = 1) ∨
      (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 2) ∨
      (coreSize P B = 3 ∧ extSize P B = 2) := by
    intro B hB
    rcases htypes B hB with h | h | ⟨e, he, -, hc, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hσ e he with h | h <;> rw [h] at hc
      · exact Or.inr (Or.inr (Or.inl ⟨hc, hb⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hc, hb⟩))
  have hslack : ∀ B ∈ Bs, slack (coreSize P B) (extSize P B) = 0 := by
    intro B hB
    rw [slack_eq_zero_iff]
    rcases htypes B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨e, he, -, hc, hb⟩
    · simp [h1, h2]
    · simp [h1, h2]
    · rcases hσ e he with h | h <;> rw [h] at hc <;> simp [hc, hb]
  have hid := slack_identity G P hBs
  rw [sum_eq_zero hslack] at hid
  have hlow := cp_ge G P
  have h1 := cp_le hBs
  have hcp : Bs.card = cp G := by omega
  have hcpZ : (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P := by omega
  -- counts
  obtain ⟨cu, cm, cs, -⟩ := type_counts G P hBs htypes4
  set k := ((extEdges G P).filter (fun e => σ e = 5)).card with hk
  have hN32 : typeCount P Bs 3 2 = k := by
    rw [typeCount_ext_eq G P hBs htypes 3, hk]
    congr 1
    apply filter_congr
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hN22 : typeCount P Bs 2 2 = ((extEdges G P).filter (fun e => ¬ σ e = 5)).card := by
    rw [typeCount_ext_eq G P hBs htypes 2]
    congr 1
    apply filter_congr
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hN12 : typeCount P Bs 1 2 = 0 := by
    rw [typeCount_ext_eq G P hBs htypes 1, card_eq_zero, filter_eq_empty_iff]
    intro e he
    rcases hσ e he with h | h <;> rw [h] <;> simp
  have hm : mCount G P = ((extEdges G P).filter (fun e => ¬ σ e = 5)).card + k := by
    rw [hk, mCount, add_comm]
    exact (card_filter_add_card_filter_not _).symm
  have hcardType : ∀ j a b, (∀ B ∈ Bs, B.card = j ↔ coreSize P B = a ∧ extSize P B = b) →
      (Bs.filter (fun B => B.card = j)).card = typeCount P Bs a b := by
    intro j a b hj
    unfold typeCount
    congr 1
    exact filter_congr hj
  have hc5 := hcardType 5 3 2 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc4 := hcardType 4 2 2 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc3 := hcardType 3 2 1 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  have hc2 := hcardType 2 1 1 (fun B hB => by
    rw [card_eq_coreSize_add_extSize P B]
    rcases htypesB B hB with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega)
  refine ⟨hcp, hcpZ, ?_, ?_, by rw [hc5, hN32], by rw [hc4]; omega,
    by rw [hc3]; omega, by rw [hc2]; omega⟩
  · intro e he
    obtain ⟨B, hB, heB⟩ := exists_block_of_edge G hBs (extEdges_subset he)
    have ht := type_of_block_containing_ext G P htypes he hB heB
    refine ⟨B, hB, heB, ?_, ht.2⟩
    rw [card_eq_coreSize_add_extSize P B, ht.1, ht.2]
    rcases hσ e he with h | h <;> omega
  · intro B hB
    rcases htypes B hB with h | h | ⟨e, he, heB, hc, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · refine Or.inr (Or.inr ⟨e, he, heB, ?_, hb⟩)
      rw [card_eq_coreSize_add_extSize P B, hc, hb]
      rcases hσ e he with h | h <;> omega

/-- **Parametric Theorem B.** Let `p = |P|`, `q = |O|` be arbitrary, `r` a load cap and
`σ : E(H) → {4,5}` a prescription. If `p + 2(h + 2r) ≤ q` and, when `h, m ≥ 1`, `r ≥ 1` and
`r (8h + 4r - 3) + 3(m - 1) ≤ r p`, then there is an optimal clique partition in which every
exterior edge `xy` lies in a block `K_{σ(xy)}` with exactly two exterior vertices, every other
block is a `(2,1)` triangle or a crossing edge, `cp(G) = s - u - 2m`, and the block counts are
`N₅ = k`, `N₄ = m - k`, `N₃ = u - m - 2k`, `N₂ = s - 2u - 2m + 2k` with `k = |σ⁻¹(5)|`. -/
theorem cp_param_B (r : ℕ) (σ : Sym2 V → ℕ) (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    (hcap : 1 ≤ editDegree G P → 1 ≤ mCount G P → 0 < r ∧
      (r : ℤ) * (8 * (editDegree G P : ℤ) + 4 * r - 3) + 3 * ((mCount G P : ℤ) - 1) ≤
        r * P.card)
    (hlist : P.card + 2 * (editDegree G P + 2 * r) ≤ Pᶜ.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
        Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  obtain ⟨Bs, hBs, htypes⟩ := exists_partition_param G P (σ := fun e => σ e - 2) (c := 3)
    (r := r) (need := 2 * (editDegree G P + 2 * r) + 3) (by norm_num)
    (fun e he => by rcases hσ e he with h | h <;> omega)
    (fun e he => by rcases hσ e he with h | h <;> rw [h] <;> omega)
    (fun h1 h2 => by
      obtain ⟨hr, hc⟩ := hcap h1 h2
      refine ⟨hr, ?_⟩
      push_cast
      linarith)
    hlist
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    prescribed_partition_conclusions G P σ hσ hBs htypes
  exact ⟨Bs, hBs, h1, h2, h2.trans (sum_formula_pq G P), h3, h4, h5, h6, h7, h8⟩

/-- **Wide-ratio Theorem B.** For every integer `t ≥ 1`, if `p + (4t+2) h ≤ q` and
`3(qh - 2) ≤ 2 t h (p - (4t+8) h + 3)`, then every prescription `σ : E(H) → {4,5}` is realised
by an optimal clique partition as in `cp_param_B` (load cap `r = t h`). In particular this
holds when `p + (4t+2)h ≤ q` and `3q ≤ 2t(p - (4t+8)h)`. -/
theorem cp_window_B (t : ℕ) (ht : 1 ≤ t) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    (hlow : P.card + (4 * t + 2) * editDegree G P ≤ Pᶜ.card)
    (hup : 3 * ((Pᶜ.card : ℤ) * editDegree G P - 2) ≤
      2 * t * editDegree G P * ((P.card : ℤ) - (4 * t + 8) * editDegree G P + 3)) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (cp G : ℤ) = (P.card : ℤ) * ((Fintype.card V : ℤ) - P.card) - (P.card.choose 2 : ℤ) +
        Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      (∀ B ∈ Bs, (coreSize P B = 2 ∧ extSize P B = 1) ∨ (coreSize P B = 1 ∧ extSize P B = 1) ∨
        ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) ∧
      ((Bs.filter (fun B => B.card = 5)).card : ℤ) =
        ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 4)).card : ℤ) =
        (mCount G P : ℤ) - ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 3)).card : ℤ) =
        (uCount G P : ℤ) - mCount G P - 2 * ((extEdges G P).filter (fun e => σ e = 5)).card ∧
      ((Bs.filter (fun B => B.card = 2)).card : ℤ) =
        (sCount G P : ℤ) - 2 * uCount G P - 2 * mCount G P +
          2 * ((extEdges G P).filter (fun e => σ e = 5)).card := by
  refine cp_param_B G P (t * editDegree G P) σ hσ (fun h1 _ => ⟨Nat.mul_pos ht h1, ?_⟩) ?_
  · have hm := two_mCount_le G P
    have hmZ : 2 * (mCount G P : ℤ) ≤ Pᶜ.card * editDegree G P := by exact_mod_cast hm
    push_cast
    nlinarith
  · nlinarith

/-- **Wide-ratio Theorem B, simplified window.** For every integer `t ≥ 1`, if
`p + (4t+2) h ≤ q` and `3q + 2t (4t+8) h ≤ 2t p`, every prescription `σ : E(H) → {4,5}` is
realised by an optimal clique partition, and `cp(G) = s - u - 2m`. -/
theorem cp_window_B_simple (t : ℕ) (ht : 1 ≤ t) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5)
    (hlow : P.card + (4 * t + 2) * editDegree G P ≤ Pᶜ.card)
    (hup : 3 * Pᶜ.card + 2 * t * (4 * t + 8) * editDegree G P ≤ 2 * t * P.card) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = (sCount G P : ℤ) - uCount G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) := by
  have hupZ : 3 * (Pᶜ.card : ℤ) + 2 * t * (4 * t + 8) * editDegree G P ≤ 2 * t * P.card := by
    exact_mod_cast hup
  have h0 : (0 : ℤ) ≤ editDegree G P := by positivity
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  obtain ⟨Bs, hBs, hcard, hcp, -, hpres, -⟩ := cp_window_B G P t ht σ hσ hlow (by nlinarith)
  exact ⟨Bs, hBs, hcard, hcp, hpres⟩

/-- **Theorem B's construction recovered from the wide-ratio theorem** (window `t = 7`), in
the manuscript setting `p = ⌊(n+1)/3⌋`, `p ≥ 63h`. -/
theorem theoremB_from_window (hP : P.card = (Fintype.card V + 1) / 3)
    (hh : 63 * editDegree G P ≤ P.card) (σ : Sym2 V → ℕ)
    (hσ : ∀ e ∈ extEdges G P, σ e = 4 ∨ σ e = 5) :
    ∃ Bs : Finset (Finset V), IsCliquePartition G Bs ∧ Bs.card = cp G ∧
      (cp G : ℤ) = Mval (Fintype.card V) + Cdef G P - Adef G P - 2 * mCount G P ∧
      (∀ e ∈ extEdges G P, ∃ B ∈ Bs, (∀ v ∈ e, v ∈ B) ∧ B.card = σ e ∧ extSize P B = 2) := by
  have hq : Pᶜ.card = Fintype.card V - P.card := card_compl P
  have hq1 : Pᶜ.card ≤ 2 * P.card + 1 := by rw [hq, hP]; exact q_le_two_p_add_one _
  have hq0 : 2 * P.card ≤ Pᶜ.card + 1 := by rw [hq, hP]; exact two_p_le_q_add_one _
  have hpq : P.card ≤ Pᶜ.card := by rw [hq, hP]; exact p_le_q _
  have hlow : P.card + (4 * 7 + 2) * editDegree G P ≤ Pᶜ.card := by
    rcases Nat.eq_zero_or_pos (editDegree G P) with h0 | h0
    · rw [h0]; omega
    · omega
  have hup : 3 * ((Pᶜ.card : ℤ) * editDegree G P - 2) ≤
      2 * ((7 : ℕ) : ℤ) * editDegree G P * ((P.card : ℤ) - (4 * ((7 : ℕ) : ℤ) + 8) *
        editDegree G P + 3) := by
    have : (Pᶜ.card : ℤ) ≤ 2 * P.card + 1 := by exact_mod_cast hq1
    have hhZ : 63 * (editDegree G P : ℤ) ≤ P.card := by exact_mod_cast hh
    have h0 : (0 : ℤ) ≤ editDegree G P := by positivity
    push_cast
    nlinarith
  obtain ⟨Bs, hBs, hcard, -, hcp, hpres, -⟩ := cp_window_B G P 7 (by norm_num) σ hσ hlow hup
  refine ⟨Bs, hBs, hcard, ?_, hpres⟩
  have hM := Mval_eq (Fintype.card V)
  rw [← hP] at hM
  have hpn : P.card ≤ Fintype.card V := card_le_univ P
  rw [hcp, hM]
  push_cast [hpn]
  ring

end PaperVI
