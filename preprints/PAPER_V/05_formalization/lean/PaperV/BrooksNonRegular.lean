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

/-
Brooks non-regular subcubic case: greedy (proved) + the <3-degree-vertex case.
Self-contained on Mathlib. Δ ≤ 3 and triangle-free ⟹ 3-colourable.
Includes the greedy lemma (A) as a helper to be proved.
-/
module

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext

@[expose] public section

open SimpleGraph

namespace PaperV.Brooks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Greedy colouring along an injective rank (helper). -/
theorem colorable_of_lower_neighbors_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (rank : V → ℕ) (hrank : Function.Injective rank)
    (h : ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card < k) :
    G.Colorable k := by
  rw [SimpleGraph.Colorable] at *
  -- We construct a coloring by greedy algorithm: for each vertex, pick a color
  -- different from all lower-ranked neighbors
  have hwf : WellFounded (fun v w => rank v < rank w) := by
    constructor
    intro a
    have key : ∀ n, ∀ a, rank a = n → Acc (fun v w => rank v < rank w) a := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro a ha
        subst ha
        refine Acc.intro a fun b hb => ih (rank b) hb b rfl
    exact key (rank a) a rfl
  -- Define the coloring using well-founded recursion
  -- For each vertex, pick a color different from lower-ranked neighbors
  let f : (v : V) → ((w : V) → rank w < rank v → Fin k) → Fin k :=
    fun v x =>
    let lowerNeighbors : Finset V := Finset.filter (fun w => rank w < rank v) (G.neighborFinset v)
    let usedColors : Finset (Fin k) := lowerNeighbors.attach.image (fun ⟨w, hw⟩ => x w (Finset.mem_filter.mp hw).2)
    have hcard : usedColors.card ≤ lowerNeighbors.attach.card := Finset.card_image_le
    have hcard2 : lowerNeighbors.attach.card = lowerNeighbors.card := Finset.card_attach
    have hlt2 : lowerNeighbors.card < k := h v
    have hlt : usedColors.card < k := Nat.lt_of_le_of_lt (hcard2 ▸ hcard) hlt2
    have hne : usedColors ≠ Finset.univ := by
      intro heq
      rw [heq] at hlt
      simp at hlt
    have hmem : ¬∀ c : Fin k, c ∈ usedColors := by
      by_contra hc
      have : usedColors = Finset.univ := Finset.eq_univ_of_forall hc
      exact hne this
    Classical.choose (not_forall.mp hmem)
  let color : V → Fin k := hwf.fix f
  -- Show color is a valid coloring
  have hcolor_eq : ∀ v, color v = f v (fun w hw => color w) := fun v => by
    show hwf.fix f v = f v (fun w hw => hwf.fix f w)
    exact WellFounded.fix_eq hwf f v
  have hcolor : ∀ u v, G.Adj u v → color u ≠ color v := by
    intro u v huv
    by_cases h : rank u < rank v
    · -- rank u < rank v: color v was chosen not to be in the set containing color u
      rw [hcolor_eq v]
      -- The color chosen by f v is not in usedColors
      -- usedColors contains color u since u is a lower-ranked neighbor
      -- First, show u ∈ lowerNeighbors
      have hu_mem : u ∈ Finset.filter (fun w => rank w < rank v) (G.neighborFinset v) := by
        simp [Finset.mem_filter, SimpleGraph.mem_neighborFinset, G.adj_symm huv, h]
      -- So color u ∈ usedColors
      let x : (w : V) → rank w < rank v → Fin k := fun w hw => color w
      have hcolor_u_mem : x u (Finset.mem_filter.mp hu_mem).2 ∈
        Finset.image (fun (p : {w // w ∈ (Finset.filter (fun w => rank w < rank v) (G.neighborFinset v))}) =>
          x p.val (Finset.mem_filter.mp p.prop).2)
          (Finset.filter (fun w => rank w < rank v) (G.neighborFinset v)).attach := by
        rw [Finset.mem_image]
        use ⟨u, hu_mem⟩
        simp
      -- The chosen color is not in usedColors
      -- By construction, Classical.choose picks an element not in the set
      have hnot_mem : ¬(f v fun w hw => color w) ∈
        Finset.image (fun (p : {w // w ∈ (Finset.filter (fun w => rank w < rank v) (G.neighborFinset v))}) =>
          (fun w hw => color w) p.val (Finset.mem_filter.mp p.prop).2)
          (Finset.filter (fun w => rank w < rank v) (G.neighborFinset v)).attach := by
        -- f v x chooses a color not in usedColors
        -- The condition used is `∃ c, c ∉ usedColors`
        simp only [f]
        exact @Classical.choose_spec (Fin k) (fun c => c ∉ _) _
      exact fun heq => hnot_mem (heq ▸ hcolor_u_mem)
    · by_cases h' : rank v < rank u
      · -- rank v < rank u: color u was chosen not to be in the set containing color v
        rw [hcolor_eq u]
        -- Symmetric to the first case
        have hv_mem : v ∈ Finset.filter (fun w => rank w < rank u) (G.neighborFinset u) := by
          simp [Finset.mem_filter, SimpleGraph.mem_neighborFinset, huv, h']
        let x : (w : V) → rank w < rank u → Fin k := fun w hw => color w
        have hcolor_v_mem : x v (Finset.mem_filter.mp hv_mem).2 ∈
          Finset.image (fun (p : {w // w ∈ (Finset.filter (fun w => rank w < rank u) (G.neighborFinset u))}) =>
            x p.val (Finset.mem_filter.mp p.prop).2)
            (Finset.filter (fun w => rank w < rank u) (G.neighborFinset u)).attach := by
          rw [Finset.mem_image]
          use ⟨v, hv_mem⟩
          simp
        have hnot_mem : ¬(f u fun w hw => color w) ∈
          Finset.image (fun (p : {w // w ∈ (Finset.filter (fun w => rank w < rank u) (G.neighborFinset u))}) =>
            (fun w hw => color w) p.val (Finset.mem_filter.mp p.prop).2)
            (Finset.filter (fun w => rank w < rank u) (G.neighborFinset u)).attach := by
          simp only [f]
          exact @Classical.choose_spec (Fin k) (fun c => c ∉ _) _
        exact fun heq => hnot_mem (heq ▸ hcolor_v_mem)
      · -- rank u = rank v: impossible since rank is injective
        exfalso
        have huvv : u = v := hrank (le_antisymm (not_lt.mp h) (not_lt.mp h')).symm
        rw [huvv] at huv
        simp at huv
  refine ⟨⟨color, ?_⟩⟩
  intro u v huv
  exact fun hne => hcolor u v huv hne

/-- **B1 primitive (closer neighbour).** In a connected graph, any `u ≠ v₀` has a neighbour `w`
strictly closer to `v₀` (the second vertex of a geodesic from `u` to `v₀`). -/
theorem exists_closer_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (v₀ u : V) (hu : u ≠ v₀) :
    ∃ w, G.Adj u w ∧ G.dist v₀ w < G.dist v₀ u := by
  have hreach : G.Reachable u v₀ := hconn.preconnected u v₀
  obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
  have hne0 : G.dist u v₀ ≠ 0 := by
    rw [ne_eq, SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable, not_or, not_not]
    exact ⟨hu, hreach⟩
  have hnp : ¬ q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  refine ⟨q.snd, ?_, ?_⟩
  · exact q.adj_snd hnp
  · have htail : G.dist q.snd v₀ ≤ q.tail.length := SimpleGraph.dist_le q.tail
    have hlen : q.tail.length + 1 = q.length := q.length_tail_add_one hnp
    have hc1 : G.dist v₀ q.snd = G.dist q.snd v₀ := SimpleGraph.dist_comm
    have hc2 : G.dist v₀ u = G.dist u v₀ := SimpleGraph.dist_comm
    rw [hc1, hc2, ← hq]
    omega

/-- A connected subcubic graph with a vertex of degree below three is three-colourable. -/
theorem connected_colorable_three_of_exists_degree_lt
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v ≤ 3) (hlow : ∃ v, G.degree v < 3) : G.Colorable 3 := by
  classical
  obtain ⟨v₀, hv₀⟩ := hlow
  set N := Fintype.card V with hN
  let e : V → ℕ := fun x => ((Fintype.equivFin V) x : ℕ)
  have he_lt : ∀ x, e x < N := fun x => ((Fintype.equivFin V) x).isLt
  have he_inj : Function.Injective e := fun a b h => (Fintype.equivFin V).injective (Fin.ext h)
  set rank : V → ℕ := fun x => N * (N - G.dist v₀ x) + e x with hrank_def
  have hrank_inj : Function.Injective rank := by
    intro a b hab
    have hmod : ∀ x, rank x % N = e x := fun x => by
      rw [hrank_def]; simp only; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (he_lt x)]
    have : e a = e b := by rw [← hmod a, ← hmod b, hab]
    exact he_inj this
  have hdist_lt : ∀ u, G.dist v₀ u < N := by
    intro u
    obtain ⟨p, hp, hlen⟩ := (hconn.preconnected v₀ u).exists_path_of_dist
    rw [← hlen]; exact hp.length_lt
  apply colorable_of_lower_neighbors_lt G 3 rank hrank_inj
  intro u
  by_cases hu : u = v₀
  · subst hu
    calc ((G.neighborFinset u).filter fun w => rank w < rank u).card
        ≤ (G.neighborFinset u).card := Finset.card_filter_le _ _
      _ = G.degree u := (G.card_neighborFinset_eq_degree u)
      _ < 3 := hv₀
  · obtain ⟨w, hadj, hwlt⟩ := exists_closer_neighbor G hconn v₀ u hu
    have hblock : N - G.dist v₀ u < N - G.dist v₀ w := by have := hdist_lt u; omega
    have hrank_wu : rank u < rank w := by
      rw [hrank_def]; simp only
      have h1 : N * (N - G.dist v₀ u) + e u < N * (N - G.dist v₀ u) + N := by
        have := he_lt u; omega
      have h2 : N * (N - G.dist v₀ u) + N ≤ N * (N - G.dist v₀ w) := by
        have hb : (N - G.dist v₀ u) + 1 ≤ (N - G.dist v₀ w) := by omega
        calc N * (N - G.dist v₀ u) + N = N * ((N - G.dist v₀ u) + 1) := by ring
          _ ≤ N * (N - G.dist v₀ w) := by gcongr
      omega
    have hwmem : w ∈ G.neighborFinset u := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hsub : ((G.neighborFinset u).filter fun x => rank x < rank u)
        ⊆ (G.neighborFinset u).erase w := by
      intro x hx
      rw [Finset.mem_filter] at hx; rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl; omega
    calc ((G.neighborFinset u).filter fun x => rank x < rank u).card
        ≤ ((G.neighborFinset u).erase w).card := Finset.card_le_card hsub
      _ = G.degree u - 1 := by rw [Finset.card_erase_of_mem hwmem, G.card_neighborFinset_eq_degree]
      _ < 3 := by have := hdeg u; omega

end PaperV.Brooks

