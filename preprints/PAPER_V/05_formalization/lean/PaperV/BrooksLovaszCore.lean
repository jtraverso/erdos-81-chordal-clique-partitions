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

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Tauto
public import PaperV.BrooksBlock
public import PaperV.BrooksB4
public import PaperV.BrooksK4
public import PaperV.BrooksLovasz
public import PaperV.BrooksLovaszEndblock

@[expose] public section
open SimpleGraph Finset

lemma connected_delete_one_then_another {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V)
    (ha : (G.induce ({a}ᶜ : Set V)).Connected)
    (hcard : 2 ≤ Fintype.card ({a}ᶜ : Set V)) :
    ∃ b : V, a ≠ b ∧ (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  have hne : ({a}ᶜ : Set V).Nonempty := by
    by_contra h
    simp [Set.not_nonempty_iff_eq_empty.mp h] at hcard
  -- Get the induced subgraph on {a}ᶜ
  set H := G.induce ({a}ᶜ : Set V) with hH
  -- H is connected with at least 2 vertices
  have hcard' : 1 < Fintype.card ({a}ᶜ : Set V) := by omega
  -- Use a maximal path in H to find a vertex whose removal preserves connectivity
  haveI : Nonempty ({a}ᶜ : Set V) := Set.nonempty_coe_sort.mpr hne
  -- Get a maximal path starting from some vertex
  have ⟨u, hu⟩ : ({a}ᶜ : Set V).Nonempty := hne
  -- Since H is connected with ≥ 2 vertices, every pair of vertices is reachable
  -- Get two distinct vertices in {a}ᶜ
  have ⟨x, hy, y, hxy⟩ := Finset.one_lt_card.mp hcard'
  -- x and y are distinct elements of {a}ᶜ
  -- Key: find a maximal path in H; its endpoints are not cut vertices
  -- Connected means Reachable for all pairs
  have hw : H.Reachable x y := ha x y
  -- We prove by contradiction: if every vertex in {a}ᶜ is a cut vertex, we get a contradiction
  by_contra hbad
  push_neg at hbad
  -- hbad says: for all b ≠ a, H.induce ({a}ᶜ \ {b}) is NOT connected
  -- We derive a contradiction using a maximal path argument
  -- Consider all walks in H; since H is finite, there's a longest simple path
  -- The endpoint of a longest simple path has degree 1 in the "spanning tree" sense
  -- Let's use the fact that there exists a simple path of maximum length
  -- We'll use a maximal path argument
  -- Consider the set of all paths in H
  -- Since H is finite, there's a path of maximum length
  -- The endpoint of such a path is not a cut vertex
  
  -- Strategy: find a vertex at maximum distance from x
  -- Such a vertex cannot be a cut vertex
  
  -- All vertices are reachable from x
  -- Consider the distance from x to each vertex
  -- By finiteness, there's a vertex at maximum distance
  
  -- Define distance function
  let dist : ({a}ᶜ : Set V) → ℕ := fun v => H.dist x v
  
  -- Find a vertex at maximum distance from x
  obtain ⟨z, _, hzmax⟩ := Finset.exists_max_image Finset.univ dist Finset.univ_nonempty
  
  -- Key claim: z is not a cut vertex
  -- Every vertex w ≠ z is reachable from x without passing through z
  -- (If the shortest path from x to w passed through z, then dist(x, w) > dist(x, z), 
  -- contradicting that z is at maximum distance)
  
  -- First, show z ≠ x (since there are ≥ 2 vertices and z is at max distance ≥ 1)
  have hzx : (z : V) ≠ x := by
    by_contra h
    have hzx' : z = x := Subtype.ext h
    rw [hzx'] at hzmax
    -- z = x, so max distance is 0
    -- But there's another vertex y ≠ x in {a}ᶜ
    have hdist_x : dist x = 0 := SimpleGraph.dist_self
    have hdist_y : dist y ≤ 0 := by simpa [hdist_x] using hzmax y (Finset.mem_univ y)
    -- So dist y = 0, meaning y = x
    have hy_eq_x : y = x := by
      have hdist_y0 : dist y = 0 := Nat.le_antisymm hdist_y (Nat.zero_le _)
      -- dist x y = 0 implies x = y or no path exists
      -- but H is connected, so there is a path, hence x = y
      unfold dist at hdist_y0
      by_cases hp : H.Reachable x y
      · obtain ⟨walk⟩ := hp
        -- dist is the minimum length, so if dist = 0 there exists a walk of length 0
        rw [SimpleGraph.dist] at hdist_y0
        by_cases h : walk.length = 0
        · cases walk.eq_of_length_eq_zero h <;> rfl
        · have hpos : 0 < walk.length := Nat.pos_of_ne_zero h
          -- If x = y, there's a walk of length 0, contradicting that dist = 0 only when x = y
          -- If x ≠ y, then every walk has length ≥ 1, so edist ≥ 1, contradicting hdist_y0
          by_contra hne
          -- Since x ≠ y, every walk has length ≥ 1
          have hall : ∀ w : H.Walk x y, 1 ≤ w.length := fun w => by
            by_contra hc
            push_neg at hc
            simp at hc
            exact hne (w.eq_of_length_eq_zero hc.length_eq_zero).symm
          -- Therefore edist ≥ 1
          haveI : Nonempty (H.Walk x y) := ⟨walk⟩
          have hedist_pos : 0 < H.edist x y := by
            unfold SimpleGraph.edist
            apply lt_of_lt_of_le (WithTop.coe_pos.mpr one_pos)
            apply le_ciInf
            intro w
            exact WithTop.coe_le_coe.mpr (hall w)
          -- This contradicts hdist_y0
          have hne_top : H.edist x y ≠ ⊤ := by
            simp only [SimpleGraph.edist]
            simp
          have h_toNat_pos : (H.edist x y).toNat > 0 := by
            have : (H.edist x y).toNat = 0 → H.edist x y = ⊤ ∨ H.edist x y = 0 := by
              intro h
              rcases H.edist x y with - | n
              · left; rfl
              · right; simp_all
            have := this hdist_y0
            rcases this with htop | hzero
            · exact absurd htop hne_top
            · simp_all
          omega
      · exact False.elim (hp (ha.preconnected x y))
    exact hxy.2 hy_eq_x.symm
  
  -- Now we have hzx : z ≠ x, and z is at maximum distance from x
  -- We claim that z is not a cut vertex: the graph remains connected after removing z
  -- because every other vertex w is reachable from x without passing through z
  
  -- First, get that a ≠ z (since z ∈ {a}ᶜ)
  have haz : a ≠ (z : V) := by
    have h : (z : V) ∈ ({a} : Set V)ᶜ := z.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
    exact fun h' => h h'.symm
  
  -- Now show that removing z keeps the graph connected
  have heq : ({a, (z : V)} : Set V) = insert a {z.val} := rfl
  have hconn : (G.induce (({a, (z : V)} : Set V)ᶜ)).Connected := by
    -- Key: z is at maximum distance from x, so every w ≠ z is reachable from x without passing through z
    -- Therefore, all vertices in V \ {a, z} are connected via x
    -- First, show the set is nonempty (it contains x, since x ≠ a and x ≠ z)
    have hxna : (x : V) ≠ a := x.2
    have hxnz : (x : V) ≠ (z : V) := hzx.symm
    set S := ({a, (z : V)} : Set V)ᶜ with hS_def
    have hne : Nonempty S := ⟨x, by simp [hS_def, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]; exact ⟨hxna, hxnz⟩⟩
    haveI := hne
    apply SimpleGraph.Connected.mk
    rintro ⟨d, hd⟩ ⟨e, he⟩
    -- d and e are in V \ {a, z}
    -- We need to show they're reachable in the induced subgraph
    -- Strategy: reach d from x without passing through z (since z is at max distance)
    -- First, get a path from x to d in H
    have hxS : (x : V) ∈ S := by
      simp [hS_def, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨hxna, hxnz⟩
    -- d ∈ S means d ≠ a and d ≠ z
    have hdne_a : (d : V) ≠ a := by simp [hS_def] at hd; tauto
    have hdne_z : (d : V) ≠ z := by simp [hS_def] at hd; tauto
    have he' : (e : V) ≠ a := by simp [hS_def] at he; tauto
    have he'z : (e : V) ≠ z := by simp [hS_def] at he; tauto
    -- The key: any vertex w in S is reachable from x without passing through z
    -- because z is at maximum distance, so the shortest path from x to w doesn't go through z
    -- First, show d is reachable from x in the induced subgraph on S
    have hd_reach : (G.induce S).Reachable ⟨x, hxS⟩ ⟨d, hd⟩ := by
      have hd_in_ac : d ∉ ({a} : Set V) := by simp [hS_def] at hd; tauto
      let d' : ({a}ᶜ : Set V) := ⟨d, hd_in_ac⟩
      have hdz_ne : z ≠ d' := by
        intro h
        have hveq : (↑z : V) = d := Subtype.ext_iff.mp h
        exact hdne_z hveq.symm
      have hdist_zd_pos : 0 < H.dist z d' := by
        have hne : z ≠ d' := hdz_ne
        simp [SimpleGraph.dist]
        -- Need to show 0 < (H.edist z d').toNat
        -- Since z ≠ d', any walk from z to d' has length ≥ 1
        have hreach : H.Reachable z d' := ha.preconnected z d'
        haveI : Nonempty (H.Walk z d') := hreach
        have hall : ∀ w : H.Walk z d', 1 ≤ w.length := fun w => by
          by_contra hc
          push_neg at hc
          simp at hc
          exact hdz_ne (w.eq_of_length_eq_zero hc.length_eq_zero)
        have hedist_pos : 0 < H.edist z d' := by
          unfold SimpleGraph.edist
          apply lt_of_lt_of_le (WithTop.coe_pos.mpr one_pos)
          apply le_ciInf
          intro w
          exact WithTop.coe_le_coe.mpr (hall w)
        have hne_top : H.edist z d' ≠ ⊤ := by
          obtain ⟨w⟩ := hreach
          have : H.edist z d' ≤ w.length := H.edist_le w
          exact ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _))
        rcases heq : H.edist z d' with - | n
        · contradiction
        · rw [heq] at hedist_pos
          rw [show (0 : ENat) = some 0 from rfl] at hedist_pos
          have hpos : 0 < n := ENat.coe_lt_coe.mp hedist_pos
          exact hpos
      have hdist_le : H.dist x d' ≤ H.dist x z := hzmax d' (Finset.mem_univ d')
      -- Key: If z were on a shortest path from x to d', then
      -- dist(x, d') = dist(x, z) + dist(z, d') ≥ dist(x, z) + 1 > dist(x, z)
      -- But dist(x, d') ≤ dist(x, z), contradiction. So shortest path avoids z.
      have hdist_xd_lt : H.dist x d' < H.dist x z + H.dist z d' := by
        by_contra hnot_lt
        push_neg at hnot_lt
        -- If dist(x, d') ≥ dist(x, z) + dist(z, d'), combined with dist(x, d') ≤ dist(x, z)
        -- we get dist(z, d') ≤ 0, contradiction with hdist_zd_pos
        have : H.dist z d' ≤ 0 := by omega
        omega
      -- Use that there exists a walk achieving the distance
      have hreach_xd : H.Reachable x d' := ha.preconnected x d'
      -- edist is the infimum of walk lengths, so there exists a walk of that length
      have hedist_ne_top : H.edist x d' ≠ ⊤ := by
        obtain ⟨w⟩ := hreach_xd
        exact ne_of_lt (lt_of_le_of_lt (H.edist_le w) (WithTop.coe_lt_top _))
      -- Key: if all walks from x to d' pass through z, then dist(x, d') ≥ dist(x, z) + dist(z, d')
      -- Since dist(x, d') < dist(x, z) + dist(z, d'), there exists a walk avoiding z
      -- We prove this by contradiction
      by_contra hall_pass_z
      -- hall_pass_z : ¬(G.induce S).Reachable x d
      -- This means all walks from x to d' in H pass through z
      -- Therefore any walk from x to d' has length ≥ dist(x, z) + dist(z, d')
      -- In particular, dist(x, d') ≥ dist(x, z) + dist(z, d'), contradicting hdist_xd_lt
      exfalso
      -- Key: hall_pass_z means all walks from x to d in H pass through z
      -- So dist_H(x, d') ≥ dist_H(x, z) + dist_H(z, d'), contradicting hdist_xd_lt
      have hcontra : H.dist x d' ≥ H.dist x z + H.dist z d' := by
        -- First show: all walks from x to d' pass through z
        -- (If there were a walk avoiding z, it would be in G.induce S, contradicting hall_pass_z)
        have hall_z : ∀ w : H.Walk x d', ∃ i ≤ w.length, w.getVert i = z := by
          intro w
          by_contra hwavoids
          push_neg at hwavoids
          -- hwavoids : ∀ j ≤ w.length, w.getVert j ≠ z
          -- Build a walk in G.induce S
          apply hall_pass_z
          -- w is a walk in H = G.induce {a}ᶜ avoiding z
          -- All vertices of w are in S = ({a, z} : Set V)ᶜ
          -- Convert w to a walk in G.induce S
          have hw_vertices : ∀ i ≤ w.length, (w.getVert i : V) ∈ S := by
            intro i hi
            simp only [hS_def, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            rw [not_or]
            exact ⟨(w.getVert i).2, by
              intro h
              apply hwavoids i hi
              exact Subtype.ext h⟩
          -- Now convert w to a walk in G.induce S
          -- We do this by induction on w
          have hall_contra : (G.induce S).Reachable ⟨x, hxS⟩ ⟨d, hd⟩ := by
            -- Define endpoint conversion from {a}ᶜ to S
            let zV : V := z.1
            have hToS : ∀ (v : ↑({a}ᶜ : Set V)), (v : V) ≠ zV → {v : V // v ∈ S} := 
              fun v hvz => ⟨v.1, fun h => by rcases h with h1 | h2 <;> [exact v.2 h1; exact hvz h2]⟩
            -- Convert subtype inequality to value inequality
            have hw_ne : ∀ i ≤ w.length, (w.getVert i : V) ≠ zV := by
              intro i hi
              exact Subtype.val_injective.ne (hwavoids i hi)
            -- Build the walk by induction
            have buildWalk_aux : ∀ {u' v' : ↑({a}ᶜ : Set V)} (p : H.Walk u' v') 
              (hp : ∀ i ≤ p.length, (p.getVert i : V) ≠ zV), 
              (G.induce S).Walk 
                (⟨(u' : V), fun h => by 
                    rcases h with h1 | h2
                    · exact u'.2 h1
                    · simp only [Set.mem_singleton_iff] at h2
                      exact hp 0 (Nat.zero_le _) (by rw [Walk.getVert_zero]; exact h2)⟩) 
                (⟨(v' : V), fun h => by 
                    rcases h with h1 | h2
                    · exact v'.2 h1
                    · simp only [Set.mem_singleton_iff] at h2
                      exact hp p.length (le_refl _) (by rw [Walk.getVert_length]; exact h2)⟩) := by
              intro u' v' p hp
              induction p with
              | nil => exact Walk.nil
              | @cons u₁ u₂ v' hw tail ih =>
                -- Get the walk for the tail
                have htail := ih (fun i hi => hp (i + 1) (by simp [Walk.length]; omega))
                -- u₁ and u₂ are in S
                have hu1S : (u₁ : V) ∈ S := by
                  simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                  exact fun h => by rcases h with h1 | h2 <;> [exact u₁.2 h1; exact hp 0 (Nat.zero_le _) h2]
                have hu2S : (u₂ : V) ∈ S := by
                  simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                  have hlen : 1 ≤ (Walk.cons hw tail).length := by simp [Walk.length]
                  exact fun h => by
                    rcases h with h1 | h2
                    · exact u₂.2 h1
                    · have := hp 1 hlen
                      rw [Walk.getVert_cons_succ, Walk.getVert_zero] at this
                      exact this h2
                -- hw : H.Adj u₁ u₂ means G.Adj (u₁ : V) (u₂ : V)
                have hadj : (G.induce S).Adj ⟨u₁, hu1S⟩ ⟨u₂, hu2S⟩ := hw
                exact Walk.cons hadj htail
            have hall_contra' : (G.induce S).Reachable ⟨x, hxS⟩ ⟨d, hd⟩ := by
              convert (buildWalk_aux w hw_ne).reachable
              all_goals apply Subtype.ext; rfl
            exact hall_contra'
          exact hall_contra
        -- Now use hall_z to derive the distance inequality
        -- All walks pass through z, so all walks have length ≥ dist(x,z) + dist(z,d')
        -- Therefore dist(x,d') ≥ dist(x,z) + dist(z,d')
        have hall_z_impl : ∀ w : H.Walk x d', (H.dist x z + H.dist z d' : ℕ∞) ≤ (w.length : ℕ∞) := by
          intro w
          obtain ⟨i, hi_le, hi_eq⟩ := hall_z w
          -- Split w into w.take i and w.drop i
          have hl1 : (w.take i).length = i := by simp [SimpleGraph.Walk.take_length, min_eq_left hi_le]
          have hl2 : (w.drop i).length = w.length - i := SimpleGraph.Walk.drop_length w i
          have h1 : H.dist x z ≤ i := by
            have hwin := H.dist_le (w.take i)
            simp only [SimpleGraph.Walk.getVert_zero, hl1, hi_eq] at hwin
            exact hwin
          have h2 : H.dist z d' ≤ w.length - i := by
            have dwin := H.dist_le (w.drop i)
            simp only [Nat.add_sub_cancel' hi_le, hl2, hi_eq] at dwin
            exact dwin
          exact_mod_cast (by omega : H.dist x z + H.dist z d' ≤ w.length)
        -- The distance is the infimum of walk lengths
        have hreach_xd : H.Reachable x d' := ha.preconnected x d'
        haveI : Nonempty (H.Walk x d') := hreach_xd
        have hedist : H.dist x z + H.dist z d' ≤ (H.edist x d').toNat := by
          have h : (H.dist x z + H.dist z d' : ℕ∞) ≤ H.edist x d' := le_ciInf hall_z_impl
          rcases heq : H.edist x d' with - | n
          · exact absurd heq (by obtain ⟨w⟩ := hreach_xd; exact ne_of_lt (lt_of_le_of_lt (H.edist_le w) (WithTop.coe_lt_top _)))
          · rw [heq] at h
            exact ENat.coe_le_coe.mp h
        exact hedist
      omega
    have he_reach : (G.induce S).Reachable ⟨x, hxS⟩ ⟨e, he⟩ := by
      have he_in_ac : e ∉ ({a} : Set V) := by simp [hS_def] at he; tauto
      let e' : ({a}ᶜ : Set V) := ⟨e, he_in_ac⟩
      have hez_ne : z ≠ e' := by
        intro h
        have hveq : (↑z : V) = e := Subtype.ext_iff.mp h
        exact he'z hveq.symm
      have hdist_ze_pos : 0 < H.dist z e' := by
        have hne : z ≠ e' := hez_ne
        simp [SimpleGraph.dist]
        have hreach : H.Reachable z e' := ha.preconnected z e'
        haveI : Nonempty (H.Walk z e') := hreach
        have hall : ∀ w : H.Walk z e', 1 ≤ w.length := fun w => by
          by_contra hc
          push_neg at hc
          simp at hc
          exact hez_ne (w.eq_of_length_eq_zero hc.length_eq_zero)
        have hedist_pos : 0 < H.edist z e' := by
          unfold SimpleGraph.edist
          apply lt_of_lt_of_le (WithTop.coe_pos.mpr one_pos)
          apply le_ciInf
          intro w
          exact WithTop.coe_le_coe.mpr (hall w)
        have hne_top : H.edist z e' ≠ ⊤ := by
          obtain ⟨w⟩ := hreach
          exact ne_of_lt (lt_of_le_of_lt (H.edist_le w) (WithTop.coe_lt_top _))
        rcases heq : H.edist z e' with - | n
        · contradiction
        · rw [heq] at hedist_pos
          rw [show (0 : ENat) = some 0 from rfl] at hedist_pos
          have hpos : 0 < n := ENat.coe_lt_coe.mp hedist_pos
          exact hpos
      have hdist_le : H.dist x e' ≤ H.dist x z := hzmax e' (Finset.mem_univ e')
      have hdist_xe_lt : H.dist x e' < H.dist x z + H.dist z e' := by
        by_contra hnot_lt
        push_neg at hnot_lt
        have : H.dist z e' ≤ 0 := by omega
        omega
      have hreach : H.Reachable x e' := ha.preconnected x e'
      by_contra hall_pass_e
      exfalso
      have hcontra : H.dist x e' ≥ H.dist x z + H.dist z e' := by
        -- Key: hall_pass_e says e is not reachable from x in G.induce S
        -- If there were a walk from x to e' in H avoiding z, it would be in G.induce S
        -- So all walks from x to e' in H must pass through z
        have hall_z : ∀ w : H.Walk x e', ∃ i ≤ w.length, w.getVert i = z := by
          intro w
          by_contra hwavoids
          push_neg at hwavoids
          apply hall_pass_e
          -- Build a walk in G.induce S from w
          have hw_vertices : ∀ i ≤ w.length, (w.getVert i : V) ∈ S := by
            intro i hi
            simp only [hS_def, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            rw [not_or]
            exact ⟨(w.getVert i).2, by
              intro h
              apply hwavoids i hi
              exact Subtype.ext h⟩
          have hall_contra' : (G.induce S).Reachable ⟨x, hxS⟩ ⟨e, he⟩ := by
            let zV : V := z.1
            have hw_ne : ∀ i ≤ w.length, (w.getVert i : V) ≠ zV := by
              intro i hi
              exact Subtype.val_injective.ne (hwavoids i hi)
            have buildWalk_aux : ∀ {u' v' : ↑({a}ᶜ : Set V)} (p : H.Walk u' v') 
              (hp : ∀ i ≤ p.length, (p.getVert i : V) ≠ zV), 
              (G.induce S).Walk 
                (⟨(u' : V), fun h => by 
                    rcases h with h1 | h2
                    · exact u'.2 h1
                    · simp only [Set.mem_singleton_iff] at h2
                      exact hp 0 (Nat.zero_le _) (by rw [Walk.getVert_zero]; exact h2)⟩) 
                (⟨(v' : V), fun h => by 
                    rcases h with h1 | h2
                    · exact v'.2 h1
                    · simp only [Set.mem_singleton_iff] at h2
                      exact hp p.length (le_refl _) (by rw [Walk.getVert_length]; exact h2)⟩) := by
              intro u' v' p hp
              induction p with
              | nil => exact Walk.nil
              | @cons u₁ u₂ v' hw tail ih =>
                have htail := ih (fun i hi => hp (i + 1) (by simp [Walk.length]; omega))
                have hu1S : (u₁ : V) ∈ S := by
                  simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                  exact fun h => by rcases h with h1 | h2 <;> [exact u₁.2 h1; exact hp 0 (Nat.zero_le _) h2]
                have hu2S : (u₂ : V) ∈ S := by
                  simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
                  have hlen : 1 ≤ (Walk.cons hw tail).length := by simp [Walk.length]
                  exact fun h => by
                    rcases h with h1 | h2
                    · exact u₂.2 h1
                    · have := hp 1 hlen
                      rw [Walk.getVert_cons_succ, Walk.getVert_zero] at this
                      exact this h2
                have hadj : (G.induce S).Adj ⟨u₁, hu1S⟩ ⟨u₂, hu2S⟩ := hw
                exact Walk.cons hadj htail
            have hall_contra'' : (G.induce S).Reachable ⟨x, hxS⟩ ⟨e, he⟩ := by
              convert (buildWalk_aux w hw_ne).reachable
              all_goals apply Subtype.ext; rfl
            exact hall_contra''
          exact hall_contra'
        -- All walks pass through z, so all walks have length ≥ dist(x,z) + dist(z,e')
        have hall_z_impl : ∀ w : H.Walk x e', (H.dist x z + H.dist z e' : ℕ∞) ≤ (w.length : ℕ∞) := by
          intro w
          obtain ⟨i, hi_le, hi_eq⟩ := hall_z w
          have hl1 : (w.take i).length = i := by simp [SimpleGraph.Walk.take_length, min_eq_left hi_le]
          have hl2 : (w.drop i).length = w.length - i := SimpleGraph.Walk.drop_length w i
          have h1 : H.dist x z ≤ i := by
            have hwin := H.dist_le (w.take i)
            simp only [SimpleGraph.Walk.getVert_zero, hl1, hi_eq] at hwin
            exact hwin
          have h2 : H.dist z e' ≤ w.length - i := by
            have dwin := H.dist_le (w.drop i)
            simp only [Nat.add_sub_cancel' hi_le, hl2, hi_eq] at dwin
            exact dwin
          exact_mod_cast (by omega : H.dist x z + H.dist z e' ≤ w.length)
        -- The distance is the infimum of walk lengths
        have hreach : H.Reachable x e' := ha.preconnected x e'
        haveI : Nonempty (H.Walk x e') := hreach
        have hedist : H.dist x z + H.dist z e' ≤ (H.edist x e').toNat := by
          have h : (H.dist x z + H.dist z e' : ℕ∞) ≤ H.edist x e' := le_ciInf hall_z_impl
          rcases heq : H.edist x e' with - | n
          · exact absurd heq (by obtain ⟨w⟩ := hreach; exact ne_of_lt (lt_of_le_of_lt (H.edist_le w) (WithTop.coe_lt_top _)))
          · rw [heq] at h
            exact ENat.coe_le_coe.mp h
        exact hedist
      omega
    -- Now compose: d → x → e
    exact (hd_reach.symm.trans he_reach)
  
  exact hbad z haz hconn

lemma connected_graph_has_deletable_pair {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  -- First, we need to find a vertex a such that G.induce ({a}ᶜ) is connected
  -- In a connected graph with ≥ 2 vertices, such a vertex exists (e.g., a leaf of a spanning tree)
  haveI : Nonempty V := hconn.nonempty
  by_cases h : ∃ a : V, (G.induce ({a}ᶜ : Set V)).Connected
  · obtain ⟨a, ha⟩ := h
    -- Now we use connected_delete_one_then_another
    have hcard_ac : 2 ≤ Fintype.card ({a}ᶜ : Set V) := by
      haveI : Fact (1 ≤ Fintype.card V) := ⟨by omega⟩
      have : Fintype.card ({a}ᶜ : Set V) = Fintype.card V - 1 := by
        simp only [Fintype.card_subtype]
        have h1 : ∀ x : V, x ∈ ({a}ᶜ : Set V) ↔ ¬x = a := by simp [Set.mem_compl_iff, Set.mem_singleton_iff]
        simp_rw [h1]
        have h2 : Finset.filter (fun x => ¬x = a) Finset.univ = Finset.univ \ {a} := by ext; simp
        simp [h2, Finset.card_sdiff, Finset.card_singleton, Finset.card_univ]
      omega
    obtain ⟨b, hab, hb⟩ := connected_delete_one_then_another G a ha hcard_ac
    exact ⟨a, b, hab, hb⟩
  · -- If no such vertex exists, then every vertex is a cut vertex
    -- This leads to a contradiction: any connected graph with ≥ 2 vertices has a non-cut vertex
    push_neg at h
    -- We use the same argument as in connected_delete_one_then_another
    -- Pick any vertex x
    obtain ⟨x⟩ := hconn.nonempty
    -- Define distance from x
    let dist : V → ℕ := fun v => G.dist x v
    -- Find a vertex at maximum distance from x
    haveI : Nonempty V := hconn.nonempty
    obtain ⟨z, _, hzmax⟩ := Finset.exists_max_image Finset.univ dist Finset.univ_nonempty
    -- z is at maximum distance from x
    -- First show z ≠ x (since |V| ≥ 3, there exists another vertex)
    have hzx : z ≠ x := by
      by_contra hzx_eq
      rw [hzx_eq] at hzmax
      -- z = x, so max distance is 0
      -- But there exists y ≠ x since |V| ≥ 3
      obtain ⟨y, hy⟩ : ∃ y : V, y ≠ x := by
        by_contra hall
        push_neg at hall
        -- All vertices equal x, so |V| = 1
        have : Fintype.card V = 1 := by
          rw [Fintype.card_eq_one_iff]
          exact ⟨x, hall⟩
        omega
      have hdist_x_zero : dist x = 0 := SimpleGraph.dist_self
      have hdist_y : dist y ≤ 0 := by simpa [hdist_x_zero] using hzmax y (Finset.mem_univ y)
      have hdist_y0 : dist y = 0 := Nat.le_antisymm hdist_y (Nat.zero_le _)
      -- dist x y = 0 and x ≠ y means no path, but G is connected
      unfold dist at hdist_y0
      rw [SimpleGraph.dist] at hdist_y0
      have hreach : G.Reachable x y := hconn x y
      haveI : Nonempty (G.Walk x y) := hreach
      have hall_walk : ∀ w : G.Walk x y, 0 < w.length := by
        intro w
        by_contra hc
        push_neg at hc
        simp at hc
        exact hy (w.eq_of_length_eq_zero hc.length_eq_zero).symm
      have hedist_pos : 0 < G.edist x y := by
        apply lt_of_lt_of_le (WithTop.coe_pos.mpr zero_lt_one)
        apply le_ciInf
        intro w
        exact WithTop.coe_le_coe.mpr (hall_walk w)
      have hne_top : G.edist x y ≠ ⊤ := by
        simp only [SimpleGraph.edist]
        simp
      have : (G.edist x y).toNat > 0 := by
        rcases heq : G.edist x y with - | n
        · contradiction
        · simp [heq] at hedist_pos ⊢
          exact ENat.coe_lt_coe.mp hedist_pos
      omega
    -- So x ∈ {z}ᶜ
    have hxin : x ∈ ({z}ᶜ : Set V) := by simp [hzx.symm]
    have hne_zc : ({z}ᶜ : Set V).Nonempty := ⟨x, hxin⟩
    haveI : Nonempty ({z}ᶜ : Set V) := Set.nonempty_coe_sort.mpr hne_zc
    -- Show that G.induce ({z}ᶜ) is connected, contradicting h
    have hcontra : (G.induce ({z}ᶜ : Set V)).Connected := by
      apply SimpleGraph.Connected.mk
      rintro ⟨d, hd⟩ ⟨e, he⟩
      -- d ≠ z and e ≠ z
      have hdne_z : (d : V) ≠ z := by simp at hd; tauto
      have he'z : (e : V) ≠ z := by simp at he; tauto
      -- Show d is reachable from x in G.induce ({z}ᶜ)
      have hd_reach : (G.induce ({z}ᶜ : Set V)).Reachable ⟨x, hxin⟩ ⟨d, hd⟩ := by
        -- Define the walk conversion first
        have buildWalk : ∀ {u v : V} (hu : u ∈ ({z}ᶜ : Set V)) (hv : v ∈ ({z}ᶜ : Set V))
          (p : G.Walk u v) (hp : ∀ i ≤ p.length, (p.getVert i : V) ∈ ({z}ᶜ : Set V)),
          (G.induce ({z}ᶜ : Set V)).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
          intro u v hu hv p hp
          induction p with
          | nil => exact Walk.nil
          | @cons u' v' w' hadj walk ih =>
            have hv' : v' ∈ ({z}ᶜ : Set V) := by
              have := hp 1 (by simp [Walk.length])
              simp at this
              exact this
            have hadj' : (G.induce ({z}ᶜ : Set V)).Adj ⟨u', hu⟩ ⟨v', hv'⟩ := hadj
            have hp' : ∀ i ≤ walk.length, (walk.getVert i : V) ∈ ({z}ᶜ : Set V) := by
              intro i hi
              exact hp (i + 1) (by simp [Walk.length]; omega)
            exact Walk.cons hadj' (ih hv' hv hp')
        -- By contradiction: assume no walk in induced graph
        by_contra hall_pass_z
        simp only [SimpleGraph.Reachable, not_exists, not_and] at hall_pass_z
        -- All walks in G from x to d must pass through z
        have hall_z : ∀ w : G.Walk x d, ∃ i ≤ w.length, w.getVert i = z := by
          intro w
          by_contra hwavoids
          push_neg at hwavoids
          exact hall_pass_z ⟨buildWalk hxin hd w hwavoids⟩
        -- Now derive distance contradiction
        -- We have hall_z: all walks from x to d pass through z
        -- So dist(x, d) ≥ dist(x, z) + dist(z, d) ≥ dist(x, z) + 1
        -- But hzmax says dist(x, d) ≤ dist(x, z), contradiction
        have hd_ne_z : (d : V) ≠ z := hdne_z
        -- d ≠ z, so dist(z, d) ≥ 1
        have hdist_zd_pos : 0 < G.dist z d := by
          simp [SimpleGraph.dist]
          have hreach_zd : G.Reachable z d := hconn z d
          haveI : Nonempty (G.Walk z d) := hreach_zd
          obtain ⟨walk_zd⟩ := hreach_zd
          have hlen : 0 < walk_zd.length := by
            by_contra h
            push_neg at h
            simp at h
            exact hd_ne_z (walk_zd.eq_of_length_eq_zero h.length_eq_zero).symm
          have hall : ∀ w : G.Walk z d, 1 ≤ w.length := fun w => by
            by_contra hc
            push_neg at hc
            simp at hc
            exact hd_ne_z (w.eq_of_length_eq_zero hc.length_eq_zero).symm
          have hedist_pos : 0 < G.edist z d := by
            apply lt_of_lt_of_le (WithTop.coe_pos.mpr zero_lt_one)
            apply le_ciInf
            intro w
            exact WithTop.coe_le_coe.mpr (hall w)
          have hne_top : G.edist z d ≠ ⊤ := by
            simp only [SimpleGraph.edist]
            simp
          rcases heq : G.edist z d with - | n
          · contradiction
          · simp [heq] at hedist_pos ⊢
            exact ENat.coe_lt_coe.mp hedist_pos
        -- Now derive the final contradiction
        -- hall_z says all walks from x to d pass through z
        -- So dist(x, d) ≥ dist(x, z) + dist(z, d) ≥ dist(x, z) + 1
        -- But hzmax says dist(x, d) ≤ dist(x, z)
        have hdist_xd_ge : G.dist x d ≥ G.dist x z + G.dist z d := by
          -- Any walk from x to d passes through z, so its length ≥ dist(x,z) + dist(z,d)
          -- Therefore dist(x,d) ≥ dist(x,z) + dist(z,d)
          have hall_len : ∀ w : G.Walk x d, w.length ≥ G.dist x z + G.dist z d := by
            intro w
            obtain ⟨i, hi_le, hi_eq⟩ := hall_z w
            have hl1 : G.dist x z ≤ i := by
              have := G.dist_le (w.take i)
              simp only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.take_length, min_eq_left hi_le, hi_eq] at this
              exact this
            have hl2 : G.dist z d ≤ w.length - i := by
              have := G.dist_le (w.drop i)
              simp only [SimpleGraph.Walk.drop_length, hi_eq] at this
              exact this
            have hik : i ≤ w.length := hi_le
            omega
          have hreach_xd : G.Reachable x d := hconn x d
          haveI : Nonempty (G.Walk x d) := hreach_xd
          simp only [SimpleGraph.dist]
          have h_edist_ge : G.edist x d ≥ (G.dist x z + G.dist z d : ℕ∞) := by
            apply le_ciInf
            intro w
            have := hall_len w
            exact WithTop.coe_le_coe.mpr this
          rcases heq : G.edist x d with - | n
          · -- edist = none means no walk, but we have hreach_xd
            have hne_top : G.edist x d ≠ ⊤ := by
              simp only [SimpleGraph.edist]
              simp [hreach_xd]
            exact absurd heq hne_top
          · simp [heq] at h_edist_ge ⊢
            exact ENat.coe_le_coe.mp h_edist_ge
        have hfinal : G.dist x d ≥ G.dist x z + 1 := by omega
        have hcontra : G.dist x d ≤ G.dist x z := hzmax d (Finset.mem_univ d)
        omega
      have he_reach : (G.induce ({z}ᶜ : Set V)).Reachable ⟨x, hxin⟩ ⟨e, he⟩ := by
        -- Define the walk conversion
        have buildWalk : ∀ {u v : V} (hu : u ∈ ({z}ᶜ : Set V)) (hv : v ∈ ({z}ᶜ : Set V))
          (p : G.Walk u v) (hp : ∀ i ≤ p.length, (p.getVert i : V) ∈ ({z}ᶜ : Set V)),
          (G.induce ({z}ᶜ : Set V)).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
          intro u v hu hv p hp
          induction p with
          | nil => exact Walk.nil
          | @cons u' v' w' hadj walk ih =>
            have hv' : v' ∈ ({z}ᶜ : Set V) := by
              have := hp 1 (by simp [Walk.length])
              simp at this
              exact this
            have hadj' : (G.induce ({z}ᶜ : Set V)).Adj ⟨u', hu⟩ ⟨v', hv'⟩ := hadj
            have hp' : ∀ i ≤ walk.length, (walk.getVert i : V) ∈ ({z}ᶜ : Set V) := by
              intro i hi
              exact hp (i + 1) (by simp [Walk.length]; omega)
            exact Walk.cons hadj' (ih hv' hv hp')
        -- By contradiction: assume no walk in induced graph
        by_contra hall_pass_z
        simp only [SimpleGraph.Reachable, not_exists, not_and] at hall_pass_z
        -- All walks in G from x to e must pass through z
        have hall_z : ∀ w : G.Walk x e, ∃ i ≤ w.length, w.getVert i = z := by
          intro w
          by_contra hwavoids
          push_neg at hwavoids
          exact hall_pass_z ⟨buildWalk hxin he w hwavoids⟩
        -- Now derive distance contradiction
        have he'_ne_z : (e : V) ≠ z := he'z
        have hdist_ze_pos : 0 < G.dist z e := by
          simp [SimpleGraph.dist]
          have hreach_z_e : G.Reachable z e := hconn z e
          haveI : Nonempty (G.Walk z e) := hreach_z_e
          have hreach_z_e' := hreach_z_e
          obtain ⟨walk_ze⟩ := hreach_z_e
          have hlen : 0 < walk_ze.length := by
            by_contra h
            push_neg at h
            simp at h
            exact he'_ne_z (walk_ze.eq_of_length_eq_zero h.length_eq_zero).symm
          have hall : ∀ w : G.Walk z e, 1 ≤ w.length := fun w => by
            by_contra hc
            push_neg at hc
            simp at hc
            exact he'_ne_z (w.eq_of_length_eq_zero hc.length_eq_zero).symm
          have hedist_pos : 0 < G.edist z e := by
            apply lt_of_lt_of_le (WithTop.coe_pos.mpr zero_lt_one)
            apply le_ciInf
            intro w
            exact WithTop.coe_le_coe.mpr (hall w)
          have hne_top : G.edist z e ≠ ⊤ := by
            obtain ⟨walk_ze⟩ := hreach_z_e'
            exact ne_of_lt (lt_of_le_of_lt (G.edist_le walk_ze) (WithTop.coe_lt_top _))
          rcases heq : G.edist z e with - | n
          · contradiction
          · simp [heq] at hedist_pos ⊢
            exact ENat.coe_lt_coe.mp hedist_pos
        have hall_len : ∀ w : G.Walk x e, w.length ≥ G.dist x z + G.dist z e := by
          intro w
          obtain ⟨i, hi_le, hi_eq⟩ := hall_z w
          have hl1 : G.dist x z ≤ i := by
            have := G.dist_le (w.take i)
            simp only [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.take_length, min_eq_left hi_le, hi_eq] at this
            exact this
          have hl2 : G.dist z e ≤ w.length - i := by
            have := G.dist_le (w.drop i)
            simp only [SimpleGraph.Walk.drop_length, hi_eq] at this
            exact this
          have hik : i ≤ w.length := hi_le
          omega
        have hreach_x_e : G.Reachable x e := hconn x e
        haveI : Nonempty (G.Walk x e) := hreach_x_e
        have h_edist_ge : G.edist x e ≥ (G.dist x z + G.dist z e : ℕ∞) := by
          apply le_ciInf
          intro w
          have := hall_len w
          exact WithTop.coe_le_coe.mpr this
        rcases heq : G.edist x e with none | n
        · obtain ⟨w⟩ := hreach_x_e
          have hle : G.edist x e ≤ w.length := G.edist_le w
          rw [heq] at hle
          exact absurd hle (not_le_of_gt (WithTop.coe_lt_top _))
        · have hdist_ge : G.dist x e ≥ G.dist x z + 1 := by
            have h1 := h_edist_ge
            rw [heq] at h1
            have h2 : (G.dist x z : ℕ) + (G.dist z e : ℕ) ≤ n := by
              simp only [← ENat.coe_add] at h1
              exact ENat.coe_le_coe.mp h1
            have h3 : 1 ≤ G.dist z e := hdist_ze_pos
            have h4 : G.dist x z + 1 ≤ G.dist x z + G.dist z e := Nat.add_le_add_left h3 (G.dist x z)
            have h5 : G.dist x z + 1 ≤ n := h4.trans h2
            have : G.dist x e = n := by rw [SimpleGraph.dist, heq]; rfl
            linarith
          have hcontra : G.dist x e ≤ G.dist x z := hzmax e (Finset.mem_univ e)
          linarith
      exact hd_reach.symm.trans he_reach
    exact (h z hcontra).elim

theorem cubic_good_triple_of_no_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hreg : ∀ v : V, G.degree v = 3)
    (hK4 : G.CliqueFree 4)
    (hnocut : ∀ x : V, (G.induce ({x}ᶜ : Set V)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨a₀, b₀, hva, hvb, hab, hnab⟩ :=
    PaperV.Brooks.exists_nonadj_pair_of_cubic_K4free G hK4 (hreg v)
  obtain ⟨u, b, hua, hub, hnab', hba⟩ :=
    PaperV.Brooks.exists_dist2_pair G hconn hab.symm hnab
  by_cases hall : ∀ y, y ≠ a₀ → (G.induce (({a₀, y} : Set V)ᶜ)).Connected
  · exact ⟨u, a₀, b, hua.symm, hub, hba.symm, hnab', hall b hba⟩
  · push_neg at hall
    obtain ⟨y, hay, hcut⟩ := hall
    by_cases hb0y : b₀ = y
    · have hvay : v ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hva.ne, fun hvy => hvb.ne (hvy.trans hb0y.symm)⟩
      exact PaperV.Brooks.good_triple_of_two_cut G hconn hreg hnocut a₀ y v hay.symm hvay hcut
    · have hb0ay : b₀ ∉ ({a₀, y} : Set V) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hab.symm, hb0y⟩
      exact PaperV.Brooks.good_triple_of_two_cut G hconn hreg hnocut a₀ y b₀ hay.symm hb0ay hcut
