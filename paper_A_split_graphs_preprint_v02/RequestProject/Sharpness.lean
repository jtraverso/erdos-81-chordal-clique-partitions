import Mathlib
import RequestProject.CliquePartition
/-!
# Sharpness of the `1/6` constant (Section 7)
We formalize the sharpness argument of Section 7 of the paper.  The extremal example is the
**complete split graph** `K_p ∨ \bar{K_q}`: a clique `C` of size `p`, an independent set `I`
of size `q`, and all edges between `C` and `I` present.
The main result (`compSplit_partition_lower`) is that *every* edge clique partition of this
graph has at least `q·p − C(p,2)` parts.  For `q = 2p` (so `n = 3p`) this gives
`2p² − C(p,2) = n²/6 + O(n)`, matching the paper's lower bound and showing that the constant
`1/6` is asymptotically sharp already for split graphs.
The proof:
* a clique contains at most one vertex of `I` (Lemma `compSplit_one_I`);
* counting the `I`–`C` edges by their covering clique gives `q·p = ∑_{K mixed} |C ∩ K|`;
* each mixed clique `K` uses `C(|C ∩ K|, 2)` clique-side edges, and these are disjoint across
  cliques, so `∑ C(|C ∩ K|, 2) ≤ C(p,2)`;
* since `n ≤ 1 + C(n,2)`, we get `q·p ≤ #(mixed cliques) + C(p,2) ≤ #P + C(p,2)`.
-/
namespace ErdosSplit
open SimpleGraph Finset
/-- The complete split graph `K_p ∨ \bar{K_q}`: the `Fin p` side is a clique, the `Fin q`
side is independent, and every cross pair is an edge. -/
def compSplit (p q : ℕ) : SimpleGraph (Fin p ⊕ Fin q) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inl b => a ≠ b
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (a | x) (b | y) h <;> simp_all [ne_comm]
  loopless := by
    constructor
    rintro (a | x) <;> simp
@[simp] theorem compSplit_adj_ll (p q : ℕ) (a b : Fin p) :
    (compSplit p q).Adj (Sum.inl a) (Sum.inl b) ↔ a ≠ b := Iff.rfl
@[simp] theorem compSplit_adj_lr (p q : ℕ) (a : Fin p) (y : Fin q) :
    (compSplit p q).Adj (Sum.inl a) (Sum.inr y) := trivial
@[simp] theorem compSplit_adj_rl (p q : ℕ) (y : Fin q) (a : Fin p) :
    (compSplit p q).Adj (Sum.inr y) (Sum.inl a) := trivial
@[simp] theorem compSplit_not_adj_rr (p q : ℕ) (x y : Fin q) :
    ¬ (compSplit p q).Adj (Sum.inr x) (Sum.inr y) := id
variable {p q : ℕ} {P : Finset (Finset (Fin p ⊕ Fin q))}
/-
A clique of the complete split graph contains at most one vertex of the independent
side `I`.
-/
theorem compSplit_one_I (hP : IsEdgeCliquePartition (compSplit p q) P)
    {K : Finset (Fin p ⊕ Fin q)} (hK : K ∈ P) {x y : Fin q}
    (hx : Sum.inr x ∈ K) (hy : Sum.inr y ∈ K) : x = y := by
  convert hP.1 K hK hx hy;
  simp +decide [ compSplit_not_adj_rr ]
/-- The clique covering the `I`–`C` edge `{inr y, inl a}` (which is an edge of the complete
split graph, so is covered by a unique member of the partition). -/
noncomputable def coverCl (hP : IsEdgeCliquePartition (compSplit p q) P)
    (y : Fin q) (a : Fin p) : Finset (Fin p ⊕ Fin q) :=
  (hP.2 (show (compSplit p q).Adj (Sum.inr y) (Sum.inl a) from trivial)).choose
theorem coverCl_mem (hP : IsEdgeCliquePartition (compSplit p q) P) (y : Fin q) (a : Fin p) :
    coverCl hP y a ∈ P :=
  (hP.2 (show (compSplit p q).Adj (Sum.inr y) (Sum.inl a) from trivial)).choose_spec.1.1
theorem coverCl_inr (hP : IsEdgeCliquePartition (compSplit p q) P) (y : Fin q) (a : Fin p) :
    Sum.inr y ∈ coverCl hP y a :=
  (hP.2 (show (compSplit p q).Adj (Sum.inr y) (Sum.inl a) from trivial)).choose_spec.1.2.1
theorem coverCl_inl (hP : IsEdgeCliquePartition (compSplit p q) P) (y : Fin q) (a : Fin p) :
    Sum.inl a ∈ coverCl hP y a :=
  (hP.2 (show (compSplit p q).Adj (Sum.inr y) (Sum.inl a) from trivial)).choose_spec.1.2.2
theorem coverCl_uniq (hP : IsEdgeCliquePartition (compSplit p q) P) (y : Fin q) (a : Fin p)
    {K : Finset (Fin p ⊕ Fin q)} (hK : K ∈ P) (hy : Sum.inr y ∈ K) (ha : Sum.inl a ∈ K) :
    K = coverCl hP y a :=
  (hP.2 (show (compSplit p q).Adj (Sum.inr y) (Sum.inl a) from trivial)).choose_spec.2 K
    ⟨hK, hy, ha⟩
/-- The clique-side (`C`) vertices of a clique `K`. -/
def Cpart (K : Finset (Fin p ⊕ Fin q)) : Finset (Fin p ⊕ Fin q) :=
  K.filter (fun w => w.isLeft)
/-- The "mixed" cliques of the partition: those containing at least one `I`-vertex and at
least one `C`-vertex. -/
noncomputable def mixed (P : Finset (Finset (Fin p ⊕ Fin q))) :
    Finset (Finset (Fin p ⊕ Fin q)) :=
  P.filter (fun K => (∃ y : Fin q, Sum.inr y ∈ K) ∧ (∃ a : Fin p, Sum.inl a ∈ K))
theorem nat_le_one_add_choose_two (n : ℕ) : n ≤ 1 + n.choose 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hstep : (m + 1).choose 2 = m + m.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega
/-
Counting the `q·p` edges between `I` and `C` by their covering clique:
`q·p = ∑_{K mixed} |C ∩ K|`.
-/
theorem compSplit_edge_count (hP : IsEdgeCliquePartition (compSplit p q) P) :
    q * p = ∑ K ∈ mixed P, (Cpart K).card := by
  have h_sum : ∀ y : Fin q, ∀ a : Fin p, ∃! K ∈ P, Sum.inr y ∈ K ∧ Sum.inl a ∈ K := by
    exact fun y a => hP.2 ( show ( compSplit p q ).Adj ( Sum.inr y ) ( Sum.inl a ) from trivial );
  choose f hf₁ hf₂ using h_sum;
  have h_sum : ∀ K ∈ mixed P, (Finset.univ.filter (fun ya : Fin q × Fin p => f ya.1 ya.2 = K)).card = (Cpart K).card := by
    intro K hK
    have h_bij : Finset.image (fun ya : Fin q × Fin p => Sum.inl ya.2) (Finset.univ.filter (fun ya : Fin q × Fin p => f ya.1 ya.2 = K)) = Cpart K := by
      ext x; simp [Cpart];
      grind +locals;
    rw [ ← h_bij, Finset.card_image_of_injOn ];
    simp +contextual [ Set.InjOn ];
    grind +suggestions;
  rw [ ← Finset.sum_congr rfl h_sum, ← Finset.card_biUnion ];
  · rw [ show ( mixed P ).biUnion ( fun x => { ya : Fin q × Fin p | f ya.1 ya.2 = x } ) = Finset.univ from ?_ ];
    · simp +decide [ Finset.card_univ ];
    · ext ⟨y, a⟩
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, Finset.mem_filter]
      exact ⟨f y a, Finset.mem_filter.mpr ⟨ hf₁ y a |>.1, ⟨ y, hf₁ y a |>.2.1 ⟩,
        ⟨ a, hf₁ y a |>.2.2 ⟩ ⟩, ⟨trivial, rfl⟩⟩
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
/-- The clique-side edges consumed by the mixed cliques are disjoint, hence their total
number `∑ C(|C ∩ K|, 2)` is at most the total number `C(p,2)` of clique-side edges. -/
theorem compSplit_pairs_bound (hP : IsEdgeCliquePartition (compSplit p q) P) :
    ∑ K ∈ mixed P, (Cpart K).card.choose 2 ≤ p.choose 2 := by
  have h_disjoint : ∀ K K' : Finset (Fin p ⊕ Fin q), K ∈ mixed P → K' ∈ mixed P → K ≠ K' → Disjoint (Finset.powersetCard 2 (Cpart K)) (Finset.powersetCard 2 (Cpart K')) := by
    intros K K' hK hK' hne
    by_contra h_not_disjoint
    obtain ⟨e, heK, heK'⟩ : ∃ e, e ∈ Finset.powersetCard 2 (Cpart K) ∧ e ∈ Finset.powersetCard 2 (Cpart K') := by
      exact Finset.not_disjoint_iff.mp h_not_disjoint;
    -- Since $e$ is a subset of both $Cpart K$ and $Cpart K'$, and $e$ has cardinality 2, it must contain two distinct elements from $Fin p$.
    obtain ⟨a, b, hab⟩ : ∃ a b : Fin p, a ≠ b ∧ Sum.inl a ∈ e ∧ Sum.inl b ∈ e := by
      simp_all +decide [ Finset.mem_powersetCard ];
      obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.1 ( by linarith ) ; simp_all +decide [ Finset.subset_iff, Cpart ] ;
      grind +splitIndPred;
    have h_unique : ∀ K K' : Finset (Fin p ⊕ Fin q), K ∈ P → K' ∈ P → Sum.inl a ∈ K → Sum.inl b ∈ K → Sum.inl a ∈ K' → Sum.inl b ∈ K' → K = K' := by
      intros K K' hK hK' ha hb ha' hb'
      have h_unique : ∃! K : Finset (Fin p ⊕ Fin q), K ∈ P ∧ Sum.inl a ∈ K ∧ Sum.inl b ∈ K := by
        exact hP.2 ( show ( compSplit p q ).Adj ( Sum.inl a ) ( Sum.inl b ) from by simp +decide [ hab.1 ] );
      exact h_unique.unique ⟨ hK, ha, hb ⟩ ⟨ hK', ha', hb' ⟩;
    exact hne <| h_unique K K' ( Finset.mem_filter.mp hK |>.1 ) ( Finset.mem_filter.mp hK' |>.1 ) ( Finset.mem_filter.mp ( Finset.mem_powersetCard.mp heK |>.1 hab.2.1 ) |>.1 ) ( Finset.mem_filter.mp ( Finset.mem_powersetCard.mp heK |>.1 hab.2.2 ) |>.1 ) ( Finset.mem_filter.mp ( Finset.mem_powersetCard.mp heK' |>.1 hab.2.1 ) |>.1 ) ( Finset.mem_filter.mp ( Finset.mem_powersetCard.mp heK' |>.1 hab.2.2 ) |>.1 );
  have h_subset : (mixed P).biUnion (fun K => Finset.powersetCard 2 (Cpart K)) ⊆ Finset.powersetCard 2 (Finset.univ.image (Sum.inl : Fin p → Fin p ⊕ Fin q)) := by
    simp +decide [ Finset.subset_iff ];
    intro x K hK hx₁ hx₂ hx₃; simp_all +decide [ Cpart ] ;
  convert Finset.card_le_card h_subset using 1;
  · rw [ Finset.card_biUnion ];
    · simp +decide [ Finset.card_powersetCard ];
    · exact fun x hx y hy hxy => h_disjoint x y hx hy hxy;
  · rw [ Finset.card_powersetCard, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]
/-- **Sharpness (per partition).** Every edge clique partition of the complete split graph
`K_p ∨ \bar{K_q}` has at least `q·p − C(p,2)` parts. -/
theorem compSplit_partition_lower (hP : IsEdgeCliquePartition (compSplit p q) P) :
    q * p - p.choose 2 ≤ P.card := by
  have hcount := compSplit_edge_count hP
  have hpairs := compSplit_pairs_bound hP
  have hsub : mixed P ⊆ P := Finset.filter_subset _ _
  have hTcard : (mixed P).card ≤ P.card := Finset.card_le_card hsub
  have hchain : q * p ≤ (mixed P).card + p.choose 2 := by
    calc q * p = ∑ K ∈ mixed P, (Cpart K).card := hcount
      _ ≤ ∑ K ∈ mixed P, (1 + (Cpart K).card.choose 2) :=
          Finset.sum_le_sum (fun K _ => nat_le_one_add_choose_two _)
      _ = (mixed P).card + ∑ K ∈ mixed P, (Cpart K).card.choose 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ (mixed P).card + p.choose 2 := by exact Nat.add_le_add_left hpairs _
  omega
/-- **Sharpness for the clique partition number.** The complete split graph `K_p ∨ \bar{K_q}`
has clique partition number at least `q·p − C(p,2)`. -/
theorem compSplit_cliquePartitionNumber_lower (p q : ℕ) :
    q * p - p.choose 2 ≤ cliquePartitionNumber (compSplit p q) := by
  haveI : DecidableRel (compSplit p q).Adj := fun _ _ => Classical.dec _
  refine le_cliquePartitionNumber _ (exists_edgeCliquePartition _) ?_
  intro P hP
  exact compSplit_partition_lower hP
/-- The complete split graph `K_p ∨ \bar{K_{2p}}` has `3p` vertices. -/
theorem compSplit_card_vertices (p : ℕ) :
    Fintype.card (Fin p ⊕ Fin (2 * p)) = 3 * p := by
  simp only [Fintype.card_sum, Fintype.card_fin]; ring
theorem two_mul_choose_two (p : ℕ) : 2 * p.choose 2 = p * (p - 1) := by
  induction p with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel, Nat.mul_add, ih]
    cases k with
    | zero => simp
    | succ j => simp only [Nat.succ_sub_one]; ring
/-- **The `1/6` lower bound is attained (up to lower order).** For the complete split graph
on `n = 3p` vertices (`q = 2p`), the clique partition number is at least `n² / 6`, in the
precise sense that `n² ≤ 6 · cp(G)`.  This exhibits a split graph witnessing the sharpness of
the constant `1/6` of the paper's main theorem. -/
theorem compSplit_sharp_lower (p : ℕ) :
    (Fintype.card (Fin p ⊕ Fin (2 * p))) ^ 2
      ≤ 6 * cliquePartitionNumber (compSplit p (2 * p)) := by
  have hlb := compSplit_cliquePartitionNumber_lower p (2 * p)
  have hcard := compSplit_card_vertices p
  have hmul : 2 * p * p = 2 * p ^ 2 := by ring
  rw [hmul] at hlb
  -- `2·C(p,2) + p = p²`, so everything is linear in the atoms `p²`, `C(p,2)`, `p`, `cp`.
  have hpp : 2 * p.choose 2 + p = p ^ 2 := by
    rw [two_mul_choose_two]
    cases p with
    | zero => simp
    | succ j => simp only [Nat.succ_sub_one]; ring
  have h9 : (3 * p) ^ 2 = 9 * p ^ 2 := by ring
  rw [hcard, h9]
  omega
end ErdosSplit
