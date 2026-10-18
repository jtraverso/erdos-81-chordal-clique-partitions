/-
Author: Juan Pablo Traverso Gianini.
Existing third-party credits below are retained.
-/
/-
Paper VI — assembly of the clique partition from the lifting blocks, the completion
triangles and the remaining crossing edges, and verification that it is an exact partition
of `E(G)` (Sections 2.3, 3, 4, 5).
-/
module

public import PaperVI.ListColoring

@[expose] public section

namespace PaperVI

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Finset V) (T : Sym2 V → Finset V) (f : V → V → V)

/-- The crossing edge `ax` was used by a lifting block. -/
def usedPair (a x : V) : Prop := ∃ e ∈ extEdges G P, a ∈ T e ∧ x ∈ e
/-- The core pair `ab` was used by a lifting block. -/
def coveredPair (a b : V) : Prop := ∃ e ∈ extEdges G P, a ∈ T e ∧ b ∈ T e
/-- Residual core edge. -/
def residPair (a b : V) : Prop := G.Adj a b ∧ ¬ coveredPair G P T a b
/-- Available crossing edge: present and unused. -/
def availPair (a x : V) : Prop := G.Adj a x ∧ ¬ usedPair G P T a x
/-- The crossing edge `ax` is used by a completion triangle. -/
def tcovPair (a x : V) : Prop := ∃ b ∈ P, b ≠ a ∧ residPair G P T a b ∧ f a b = x

instance (a x : V) : Decidable (usedPair G P T a x) := by unfold usedPair; infer_instance
instance (a x : V) : Decidable (coveredPair G P T a x) := by unfold coveredPair; infer_instance
instance (a x : V) : Decidable (residPair G P T a x) := by unfold residPair; infer_instance
instance (a x : V) : Decidable (availPair G P T a x) := by unfold availPair; infer_instance
instance (a x : V) : Decidable (tcovPair G P T f a x) := by unfold tcovPair; infer_instance

/-- The lifting blocks `T e ∪ e`. -/
def liftBlocks : Finset (Finset V) := (extEdges G P).image (fun e => T e ∪ e.toFinset)

/-- The completion triangles `{a, b, f a b}` over residual core edges. -/
def triBlocks : Finset (Finset V) :=
  ((P ×ˢ P).filter (fun ab => ab.1 ≠ ab.2 ∧ residPair G P T ab.1 ab.2)).image
    (fun ab => ({ab.1, ab.2, f ab.1 ab.2} : Finset V))

/-- The remaining crossing edges, as single-edge blocks. -/
def edgeBlocks : Finset (Finset V) :=
  ((P ×ˢ Pᶜ).filter (fun ax => availPair G P T ax.1 ax.2 ∧ ¬ tcovPair G P T f ax.1 ax.2)).image
    (fun ax => ({ax.1, ax.2} : Finset V))

/-- The assembled family of blocks. -/
def allBlocks : Finset (Finset V) := liftBlocks G P T ∪ triBlocks G P T f ∪ edgeBlocks G P T f

variable {G P T f}

theorem mem_liftBlocks {B : Finset V} :
    B ∈ liftBlocks G P T ↔ ∃ e ∈ extEdges G P, T e ∪ e.toFinset = B := by
  simp [liftBlocks]

theorem mem_triBlocks {B : Finset V} :
    B ∈ triBlocks G P T f ↔ ∃ a b, a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ residPair G P T a b ∧
      ({a, b, f a b} : Finset V) = B := by
  unfold triBlocks
  rw [mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [mem_filter, mem_product] at hab
    exact ⟨a, b, hab.1.1, hab.1.2, hab.2.1, hab.2.2, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, hr, rfl⟩
    exact ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab, hr⟩, rfl⟩

theorem mem_edgeBlocks {B : Finset V} :
    B ∈ edgeBlocks G P T f ↔ ∃ a x, a ∈ P ∧ x ∉ P ∧ availPair G P T a x ∧
      ¬ tcovPair G P T f a x ∧ ({a, x} : Finset V) = B := by
  unfold edgeBlocks
  rw [mem_image]
  constructor
  · rintro ⟨⟨a, x⟩, hax, rfl⟩
    rw [mem_filter, mem_product, mem_compl] at hax
    exact ⟨a, x, hax.1.1, hax.1.2, hax.2.1, hax.2.2, rfl⟩
  · rintro ⟨a, x, ha, hx, hav, ht, rfl⟩
    exact ⟨(a, x), mem_filter.mpr ⟨mem_product.mpr ⟨ha, mem_compl.mpr hx⟩, hav, ht⟩, rfl⟩

theorem not_mem_of_mem_extEdges {e : Sym2 V} (he : e ∈ extEdges G P) {v : V} (hv : v ∈ e) :
    v ∉ P := by
  simp only [extEdges, mem_filter, Sym2.mem_toFinset] at he
  exact he.2 v hv

theorem adj_of_mem_extEdges {e : Sym2 V} (he : e ∈ extEdges G P) {u v : V} (hu : u ∈ e)
    (hv : v ∈ e) (huv : u ≠ v) : G.Adj u v := by
  simp only [extEdges, mem_filter, SimpleGraph.mem_edgeFinset] at he
  rw [(Sym2.mem_and_mem_iff huv).mp ⟨hu, hv⟩] at he
  exact he.1

section blocks

variable {σ : Sym2 V → ℕ} {r : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
include hT

omit hT in
theorem mem_lift_core {e : Sym2 V} (he : e ∈ extEdges G P) {v : V} (hv : v ∈ P) :
    v ∈ T e ∪ e.toFinset ↔ v ∈ T e := by
  rw [mem_union, Sym2.mem_toFinset]
  exact ⟨fun h => h.elim id (fun h' => absurd hv (not_mem_of_mem_extEdges he h')), Or.inl⟩

theorem mem_lift_ext {e : Sym2 V} (he : e ∈ extEdges G P) {v : V} (hv : v ∉ P) :
    v ∈ T e ∪ e.toFinset ↔ v ∈ e := by
  rw [mem_union, Sym2.mem_toFinset]
  exact ⟨fun h => h.elim (fun h' => absurd (hT.sub e he h') hv) id, Or.inr⟩

end blocks

omit [Fintype V] in
theorem mem_tri_core {a b c v : V} (hc : c ∉ P) (hv : v ∈ P) :
    v ∈ ({a, b, c} : Finset V) ↔ v = a ∨ v = b := by
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (h | h | rfl)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hv hc
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

omit [Fintype V] in
theorem mem_tri_ext {a b c v : V} (ha : a ∈ P) (hb : b ∈ P) (hv : v ∉ P) :
    v ∈ ({a, b, c} : Finset V) ↔ v = c := by
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | rfl | h)
    · exact absurd ha hv
    · exact absurd hb hv
    · exact h
  · intro h; exact Or.inr (Or.inr h)

omit [Fintype V] in
theorem mem_pair_core {a x v : V} (hx : x ∉ P) (hv : v ∈ P) :
    v ∈ ({a, x} : Finset V) ↔ v = a := by
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact absurd hv hx
  · exact Or.inl

omit [Fintype V] in
theorem mem_pair_ext {a x v : V} (ha : a ∈ P) (hv : v ∉ P) :
    v ∈ ({a, x} : Finset V) ↔ v = x := by
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro (rfl | h)
    · exact absurd ha hv
    · exact h
  · exact Or.inr

theorem extEdges_subset : extEdges G P ⊆ G.edgeFinset := by
  intro e he
  simp only [extEdges, mem_filter] at he
  exact he.1

theorem coveredPair_symm {a b : V} (h : coveredPair G P T a b) : coveredPair G P T b a := by
  obtain ⟨e, he, ha, hb⟩ := h; exact ⟨e, he, hb, ha⟩

theorem residPair_symm {a b : V} (h : residPair G P T a b) : residPair G P T b a :=
  ⟨h.1.symm, fun h' => h.2 (coveredPair_symm h')⟩

section partition

variable {σ : Sym2 V → ℕ} {r : ℕ} (hT : LiftInv G P σ r (extEdges G P) T)
  (hf1 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b → f a b = f b a)
  (hf2 : ∀ a ∈ P, ∀ b ∈ P, a ≠ b → residPair G P T a b →
    f a b ∉ P ∧ availPair G P T a (f a b) ∧ availPair G P T b (f a b))
  (hf3 : ∀ a ∈ P, ∀ b ∈ P, ∀ b' ∈ P, a ≠ b → a ≠ b' → b ≠ b' → residPair G P T a b →
    residPair G P T a b' → f a b ≠ f a b')

theorem lift_core {B : Finset V} (hB : B ∈ liftBlocks G P T) {u v : V} (hu : u ∈ P)
    (hv : v ∈ P) (huB : u ∈ B) (hvB : v ∈ B) :
    ∃ e ∈ extEdges G P, u ∈ T e ∧ v ∈ T e ∧ B = T e ∪ e.toFinset := by
  obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
  exact ⟨e, he, (mem_lift_core he hu).mp huB, (mem_lift_core he hv).mp hvB, rfl⟩

include hT in
theorem lift_cross {B : Finset V} (hB : B ∈ liftBlocks G P T) {a x : V} (ha : a ∈ P)
    (hx : x ∉ P) (haB : a ∈ B) (hxB : x ∈ B) :
    ∃ e ∈ extEdges G P, a ∈ T e ∧ x ∈ e ∧ B = T e ∪ e.toFinset := by
  obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
  exact ⟨e, he, (mem_lift_core he ha).mp haB, (mem_lift_ext hT he hx).mp hxB, rfl⟩

include hT in
theorem lift_ext {B : Finset V} (hB : B ∈ liftBlocks G P T) {u v : V} (hu : u ∉ P)
    (hv : v ∉ P) (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B) :
    B = T s(u, v) ∪ s(u, v).toFinset := by
  obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
  have h1 := (mem_lift_ext hT he hu).mp huB
  have h2 := (mem_lift_ext hT he hv).mp hvB
  rw [(Sym2.mem_and_mem_iff huv).mp ⟨h1, h2⟩]

include hf1 hf2 in
theorem tri_core {B : Finset V} (hB : B ∈ triBlocks G P T f) {u v : V} (hu : u ∈ P)
    (hv : v ∈ P) (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B) :
    residPair G P T u v ∧ B = {u, v, f u v} := by
  obtain ⟨a, b, ha, hb, hab, hres, rfl⟩ := mem_triBlocks.mp hB
  have hc := (hf2 a ha b hb hab hres).1
  rw [mem_tri_core hc hu] at huB
  rw [mem_tri_core hc hv] at hvB
  rcases huB with rfl | rfl <;> rcases hvB with rfl | rfl
  · exact absurd rfl huv
  · exact ⟨hres, rfl⟩
  · refine ⟨residPair_symm hres, ?_⟩
    rw [hf1 u hu v hv huv (residPair_symm hres), Finset.insert_comm]
  · exact absurd rfl huv

include hf1 hf2 in
theorem tri_cross {B : Finset V} (hB : B ∈ triBlocks G P T f) {a x : V} (ha : a ∈ P)
    (hx : x ∉ P) (haB : a ∈ B) (hxB : x ∈ B) :
    ∃ b ∈ P, b ≠ a ∧ residPair G P T a b ∧ f a b = x ∧ B = {a, b, f a b} := by
  obtain ⟨a', b', ha', hb', hab', hres, rfl⟩ := mem_triBlocks.mp hB
  have hc := (hf2 a' ha' b' hb' hab' hres).1
  rw [mem_tri_core hc ha] at haB
  rw [mem_tri_ext ha' hb' hx] at hxB
  rcases haB with rfl | rfl
  · exact ⟨b', hb', hab'.symm, hres, hxB.symm, rfl⟩
  · refine ⟨a', ha', hab', residPair_symm hres, ?_, ?_⟩
    · rw [hf1 a ha a' ha' hab'.symm (residPair_symm hres)]; exact hxB.symm
    · rw [hf1 a ha a' ha' hab'.symm (residPair_symm hres), Finset.insert_comm]

theorem tri_ext {B : Finset V} (hB : B ∈ triBlocks G P T f) {u v : V} (hu : u ∉ P)
    (hv : v ∉ P) (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B) : False := by
  obtain ⟨a, b, ha, hb, hab, hres, rfl⟩ := mem_triBlocks.mp hB
  rw [mem_tri_ext ha hb hu] at huB
  rw [mem_tri_ext ha hb hv] at hvB
  exact huv (huB.trans hvB.symm)

theorem edge_core {B : Finset V} (hB : B ∈ edgeBlocks G P T f) {u v : V} (hu : u ∈ P)
    (hv : v ∈ P) (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B) : False := by
  obtain ⟨a, x, ha, hx, -, -, rfl⟩ := mem_edgeBlocks.mp hB
  rw [mem_pair_core hx hu] at huB
  rw [mem_pair_core hx hv] at hvB
  exact huv (huB.trans hvB.symm)

theorem edge_cross {B : Finset V} (hB : B ∈ edgeBlocks G P T f) {a x : V} (ha : a ∈ P)
    (hx : x ∉ P) (haB : a ∈ B) (hxB : x ∈ B) :
    availPair G P T a x ∧ ¬ tcovPair G P T f a x ∧ B = {a, x} := by
  obtain ⟨a', x', ha', hx', hav, ht, rfl⟩ := mem_edgeBlocks.mp hB
  rw [mem_pair_core hx' ha] at haB
  rw [mem_pair_ext ha' hx] at hxB
  subst haB hxB
  exact ⟨hav, ht, rfl⟩

theorem edge_ext {B : Finset V} (hB : B ∈ edgeBlocks G P T f) {u v : V} (hu : u ∉ P)
    (hv : v ∉ P) (huv : u ≠ v) (huB : u ∈ B) (hvB : v ∈ B) : False := by
  obtain ⟨a, x, ha, hx, -, -, rfl⟩ := mem_edgeBlocks.mp hB
  rw [mem_pair_ext ha hu] at huB
  rw [mem_pair_ext ha hv] at hvB
  exact huv (huB.trans hvB.symm)

omit [Fintype V] [DecidableEq V] in
theorem existsUnique_of {Bs : Finset (Finset V)} {u v : V} (B0 : Finset V)
    (h0 : B0 ∈ Bs ∧ u ∈ B0 ∧ v ∈ B0) (h : ∀ B ∈ Bs, u ∈ B → v ∈ B → B = B0) :
    ∃! B, B ∈ Bs ∧ u ∈ B ∧ v ∈ B :=
  ⟨B0, h0, fun B hB => h B hB.1 hB.2.1 hB.2.2⟩

theorem mem_allBlocks {B : Finset V} : B ∈ allBlocks G P T f ↔
    B ∈ liftBlocks G P T ∨ B ∈ triBlocks G P T f ∨ B ∈ edgeBlocks G P T f := by
  simp only [allBlocks, mem_union, or_assoc]

include hT hf1 hf2 in
theorem existsUnique_core {u v : V} (hu : u ∈ P) (hv : v ∈ P) (huv : G.Adj u v) :
    ∃! B, B ∈ allBlocks G P T f ∧ u ∈ B ∧ v ∈ B := by
  have hne := huv.ne
  by_cases hc : coveredPair G P T u v
  · obtain ⟨e, he, hue, hve⟩ := hc
    refine existsUnique_of (T e ∪ e.toFinset)
      ⟨mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨e, he, rfl⟩)), mem_union_left _ hue,
        mem_union_left _ hve⟩ ?_
    intro B hB huB hvB
    rcases mem_allBlocks.mp hB with hB | hB | hB
    · obtain ⟨e', he', hue', hve', rfl⟩ := lift_core hB hu hv huB hvB
      by_contra hne'
      have hee' : e ≠ e' := fun h => hne' (h ▸ rfl)
      exact hT.pairDisj e he e' he' hee' u hue v hve hne hue' hve'
    · exact absurd ⟨e, he, hue, hve⟩ (tri_core hf1 hf2 hB hu hv hne huB hvB).1.2
    · exact (edge_core hB hu hv hne huB hvB).elim
  · have hres : residPair G P T u v := ⟨huv, hc⟩
    refine existsUnique_of {u, v, f u v}
      ⟨mem_allBlocks.mpr (Or.inr (Or.inl (mem_triBlocks.mpr ⟨u, v, hu, hv, hne, hres, rfl⟩))),
        by simp, by simp⟩ ?_
    intro B hB huB hvB
    rcases mem_allBlocks.mp hB with hB | hB | hB
    · obtain ⟨e', he', hue', hve', rfl⟩ := lift_core hB hu hv huB hvB
      exact absurd ⟨e', he', hue', hve'⟩ hc
    · exact (tri_core hf1 hf2 hB hu hv hne huB hvB).2
    · exact (edge_core hB hu hv hne huB hvB).elim

include hT hf1 hf2 hf3 in
theorem existsUnique_cross {a x : V} (ha : a ∈ P) (hx : x ∉ P) (hax : G.Adj a x) :
    ∃! B, B ∈ allBlocks G P T f ∧ a ∈ B ∧ x ∈ B := by
  by_cases hu : usedPair G P T a x
  · obtain ⟨e, he, hae, hxe⟩ := hu
    refine existsUnique_of (T e ∪ e.toFinset)
      ⟨mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨e, he, rfl⟩)), mem_union_left _ hae,
        mem_union_right _ (Sym2.mem_toFinset.mpr hxe)⟩ ?_
    intro B hB haB hxB
    rcases mem_allBlocks.mp hB with hB | hB | hB
    · obtain ⟨e', he', hae', hxe', rfl⟩ := lift_cross hT hB ha hx haB hxB
      by_contra hne'
      have hee' : e ≠ e' := fun h => hne' (h ▸ rfl)
      exact hT.incDisj e he e' he' hee' x hxe hxe' a hae hae'
    · obtain ⟨b, hb, hba, hres', hfx, -⟩ := tri_cross hf1 hf2 hB ha hx haB hxB
      have := (hf2 a ha b hb hba.symm hres').2.1
      rw [hfx] at this
      exact absurd ⟨e, he, hae, hxe⟩ this.2
    · exact absurd ⟨e, he, hae, hxe⟩ (edge_cross hB ha hx haB hxB).1.2
  · by_cases ht : tcovPair G P T f a x
    · obtain ⟨b, hb, hba, hres, hfx⟩ := ht
      refine existsUnique_of {a, b, f a b}
        ⟨mem_allBlocks.mpr (Or.inr (Or.inl (mem_triBlocks.mpr
          ⟨a, b, ha, hb, hba.symm, hres, rfl⟩))), by simp, by simp [hfx]⟩ ?_
      intro B hB haB hxB
      rcases mem_allBlocks.mp hB with hB | hB | hB
      · obtain ⟨e', he', hae', hxe', -⟩ := lift_cross hT hB ha hx haB hxB
        exact absurd ⟨e', he', hae', hxe'⟩ hu
      · obtain ⟨b', hb', hba', hres', hfx', rfl⟩ := tri_cross hf1 hf2 hB ha hx haB hxB
        by_contra hne
        have hbb : b' ≠ b := fun h => hne (h ▸ rfl)
        exact hf3 a ha b' hb' b hb hba'.symm hba.symm hbb hres' hres (hfx'.trans hfx.symm)
      · exact absurd ⟨b, hb, hba, hres, hfx⟩ (edge_cross hB ha hx haB hxB).2.1
    · refine existsUnique_of {a, x}
        ⟨mem_allBlocks.mpr (Or.inr (Or.inr (mem_edgeBlocks.mpr
          ⟨a, x, ha, hx, ⟨hax, hu⟩, ht, rfl⟩))), by simp, by simp⟩ ?_
      intro B hB haB hxB
      rcases mem_allBlocks.mp hB with hB | hB | hB
      · obtain ⟨e', he', hae', hxe', -⟩ := lift_cross hT hB ha hx haB hxB
        exact absurd ⟨e', he', hae', hxe'⟩ hu
      · obtain ⟨b, hb, hba, hres, hfx, -⟩ := tri_cross hf1 hf2 hB ha hx haB hxB
        exact absurd ⟨b, hb, hba, hres, hfx⟩ ht
      · exact (edge_cross hB ha hx haB hxB).2.2

include hT hf2 in
omit hf2 in
theorem existsUnique_ext {u v : V} (hu : u ∉ P) (hv : v ∉ P) (huv : G.Adj u v) :
    ∃! B, B ∈ allBlocks G P T f ∧ u ∈ B ∧ v ∈ B := by
  have hne := huv.ne
  have he : s(u, v) ∈ extEdges G P := (mem_extEdges G P).mpr ⟨huv, hu, hv⟩
  refine existsUnique_of (T s(u, v) ∪ s(u, v).toFinset)
    ⟨mem_allBlocks.mpr (Or.inl (mem_liftBlocks.mpr ⟨_, he, rfl⟩)),
      mem_union_right _ (by simp), mem_union_right _ (by simp)⟩ ?_
  intro B hB huB hvB
  rcases mem_allBlocks.mp hB with hB | hB | hB
  · exact lift_ext hT hB hu hv hne huB hvB
  · exact (tri_ext hB hu hv hne huB hvB).elim
  · exact (edge_ext hB hu hv hne huB hvB).elim

include hT hf1 hf2 hf3 in
/-- The assembled family is a clique partition of `G`. -/
theorem allBlocks_isCliquePartition : IsCliquePartition G (allBlocks G P T f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    rcases mem_allBlocks.mp hB with hB | hB | hB
    · obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
      have hnd := G.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp (extEdges_subset he))
      calc 2 = e.toFinset.card := (Sym2.card_toFinset_of_not_isDiag e hnd).symm
        _ ≤ _ := card_le_card subset_union_right
    · obtain ⟨a, b, ha, hb, hab, -, rfl⟩ := mem_triBlocks.mp hB
      exact one_lt_card.mpr ⟨a, by simp, b, by simp, hab⟩
    · obtain ⟨a, x, ha, hx, -, -, rfl⟩ := mem_edgeBlocks.mp hB
      exact one_lt_card.mpr ⟨a, by simp, x, by simp, fun h => hx (h ▸ ha)⟩
  · intro B hB u hu v hv huv
    rw [mem_coe] at hu hv
    rcases mem_allBlocks.mp hB with hB | hB | hB
    · obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
      rw [mem_union, Sym2.mem_toFinset] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hT.coreAdj e he u hu v hv huv
      · exact hT.crossAdj e he u hu v hv
      · exact (hT.crossAdj e he v hv u hu).symm
      · exact adj_of_mem_extEdges he hu hv huv
    · obtain ⟨a, b, ha, hb, hab, hres, rfl⟩ := mem_triBlocks.mp hB
      have h1 := hres.1
      have h2 := (hf2 a ha b hb hab hres).2.1.1
      have h3 := (hf2 a ha b hb hab hres).2.2.1
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first | exact absurd rfl huv | assumption | exact SimpleGraph.Adj.symm ‹_›
    · obtain ⟨a, x, ha, hx, hav, -, rfl⟩ := mem_edgeBlocks.mp hB
      simp only [mem_insert, mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact hav.1
      · exact hav.1.symm
      · exact absurd rfl huv
  · intro u v huv
    by_cases hu : u ∈ P <;> by_cases hv : v ∈ P
    · exact existsUnique_core hT hf1 hf2 hu hv huv
    · exact existsUnique_cross hT hf1 hf2 hf3 hu hv huv
    · obtain ⟨B, hB, hBu⟩ := existsUnique_cross hT hf1 hf2 hf3 hv hu huv.symm
      exact ⟨B, ⟨hB.1, hB.2.2, hB.2.1⟩, fun B' hB' => hBu B' ⟨hB'.1, hB'.2.2, hB'.2.1⟩⟩
    · exact existsUnique_ext hT hu hv huv

include hT hf2 in
/-- Every assembled block has type `(1,1)`, `(2,1)`, or `(σ e, 2)` around an exterior edge `e`. -/
theorem allBlocks_types {B : Finset V} (hB : B ∈ allBlocks G P T f) :
    (coreSize P B = 1 ∧ extSize P B = 1) ∨ (coreSize P B = 2 ∧ extSize P B = 1) ∨
      ∃ e ∈ extEdges G P, (∀ v ∈ e, v ∈ B) ∧ coreSize P B = σ e ∧ extSize P B = 2 := by
  rcases mem_allBlocks.mp hB with hB | hB | hB
  · obtain ⟨e, he, rfl⟩ := mem_liftBlocks.mp hB
    right; right
    refine ⟨e, he, fun v hv => mem_union_right _ (Sym2.mem_toFinset.mpr hv), ?_, ?_⟩
    · unfold coreSize
      have : (T e ∪ e.toFinset) ∩ P = T e := by
        ext v
        rw [mem_inter]
        constructor
        · rintro ⟨h1, h2⟩; exact (mem_lift_core he h2).mp h1
        · intro h; exact ⟨mem_union_left _ h, hT.sub e he h⟩
      rw [this, hT.card e he]
    · unfold extSize
      have : (T e ∪ e.toFinset) \ P = e.toFinset := by
        ext v
        rw [mem_sdiff]
        constructor
        · rintro ⟨h1, h2⟩; exact Sym2.mem_toFinset.mpr ((mem_lift_ext hT he h2).mp h1)
        · intro h
          exact ⟨mem_union_right _ h, not_mem_of_mem_extEdges he (Sym2.mem_toFinset.mp h)⟩
      rw [this]
      exact Sym2.card_toFinset_of_not_isDiag e
        (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (extEdges_subset he)))
  · obtain ⟨a, b, ha, hb, hab, hres, rfl⟩ := mem_triBlocks.mp hB
    have hc := (hf2 a ha b hb hab hres).1
    right; left
    constructor
    · unfold coreSize
      have : ({a, b, f a b} : Finset V) ∩ P = {a, b} := by
        ext v
        rw [mem_inter]
        constructor
        · rintro ⟨h1, h2⟩; rw [mem_tri_core hc h2] at h1; simpa using h1
        · intro h
          simp only [mem_insert, mem_singleton] at h
          rcases h with rfl | rfl
          · exact ⟨by simp, ha⟩
          · exact ⟨by simp, hb⟩
      rw [this, card_pair hab]
    · unfold extSize
      have : ({a, b, f a b} : Finset V) \ P = {f a b} := by
        ext v
        rw [mem_sdiff, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact (mem_tri_ext ha hb h2).mp h1
        · rintro rfl; exact ⟨by simp, hc⟩
      rw [this, card_singleton]
  · obtain ⟨a, x, ha, hx, -, -, rfl⟩ := mem_edgeBlocks.mp hB
    left
    constructor
    · unfold coreSize
      have : ({a, x} : Finset V) ∩ P = {a} := by
        ext v
        rw [mem_inter, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact (mem_pair_core hx h2).mp h1
        · rintro rfl; exact ⟨by simp, ha⟩
      rw [this, card_singleton]
    · unfold extSize
      have : ({a, x} : Finset V) \ P = {x} := by
        ext v
        rw [mem_sdiff, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact (mem_pair_ext ha h2).mp h1
        · rintro rfl; exact ⟨by simp, hx⟩
      rw [this, card_singleton]

end partition

end PaperVI
