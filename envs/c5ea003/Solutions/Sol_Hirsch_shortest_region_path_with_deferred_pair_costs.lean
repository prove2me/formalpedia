-- Prove2me | solution 1 for Hirsch.shortest_region_path_with_deferred_pair_costs
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T15:58:39.109194+00:00
-- url     : https://prove2.me/submissions/59a4c70a-7584-4f2e-a429-23598e316dd8

import Mathlib

/-!
# Choose the region path and its portal pairs before proving local costs

The same finite list of actual portal pairs works for every subsequent routing
graph and cost assignment. Only pairs in this list need local routes. This
quantifier order permits costs to depend on the chosen chordless support.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000


private theorem region_walk_deferred_costs
    {V ι : Type*} (S : ι → Set V) (G : SimpleGraph ι)
    (hoverlap : ∀ i j, G.Adj i j → ∃ z, z ∈ S i ∧ z ∈ S j)
    {i j : ι} (p : G.Walk i j) :
    ∀ u ∈ S i, ∀ v ∈ S j,
      ∃ legs : List (ι × V × V),
        legs.map Prod.fst = p.support ∧
        (∀ leg ∈ legs, leg.2.1 ∈ S leg.1 ∧ leg.2.2 ∈ S leg.1) ∧
        ∀ (H : SimpleGraph V) (C : ι → V → V → ℕ),
          (∀ leg ∈ legs, ∃ q : H.Walk leg.2.1 leg.2.2,
            q.length ≤ C leg.1 leg.2.1 leg.2.2) →
          ∃ q : H.Walk u v,
            q.length ≤ (legs.map fun leg => C leg.1 leg.2.1 leg.2.2).sum := by
  induction p with
  | @nil i =>
      intro u hu v hv
      refine ⟨[(i, u, v)], by simp, ?_, ?_⟩
      · intro leg hleg
        rcases List.mem_singleton.mp hleg with rfl
        exact ⟨hu, hv⟩
      · intro H C hlocal
        simpa using hlocal (i, u, v) (by simp)
  | @cons i k j hik p ih =>
      intro u hu v hv
      obtain ⟨z, hzi, hzk⟩ := hoverlap i k hik
      obtain ⟨legs, hlabels, hfits, hroute⟩ := ih z hzk v hv
      refine ⟨(i, u, z) :: legs, by simp [hlabels], ?_, ?_⟩
      · intro leg hleg
        rcases List.mem_cons.mp hleg with rfl | hleg
        · exact ⟨hu, hzi⟩
        · exact hfits leg hleg
      · intro H C hlocal
        obtain ⟨first, hfirst⟩ := hlocal (i, u, z) (by simp)
        obtain ⟨tail, htail⟩ := hroute H C (fun leg hleg =>
          hlocal leg (List.mem_cons_of_mem _ hleg))
        refine ⟨first.append tail, ?_⟩
        simpa using Nat.add_le_add hfirst htail

/-- Region geometry is fixed before any local routing obligations are supplied.
Choose a shortest (hence chordless) path in a region graph whose adjacent labels
have overlapping regions. There is one duplicate-free list of actual portal
pairs, labelled by that path's support, such that routes for just those pairs
assemble with additive cost. The routing graph and costs are universally
quantified *after* the path and pairs have been chosen. -/
theorem solution
    {V ι : Type*} (S : ι → Set V) (G : SimpleGraph ι)
    (hoverlap : ∀ i j, G.Adj i j → ∃ z, z ∈ S i ∧ z ∈ S j)
    {i j : ι} (hreach : G.Reachable i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : G.Walk i j,
      p.length = G.dist i j ∧ p.IsPath ∧
      (∀ r s : ℕ, r + 1 < s → s ≤ p.length →
        ¬ G.Adj (p.getVert r) (p.getVert s)) ∧
      ∃ legs : List (ι × V × V),
        legs.map Prod.fst = p.support ∧
        (legs.map Prod.fst).Nodup ∧
        (∀ leg ∈ legs, leg.2.1 ∈ S leg.1 ∧ leg.2.2 ∈ S leg.1) ∧
        ∀ (H : SimpleGraph V) (C : ι → V → V → ℕ),
          (∀ leg ∈ legs, ∃ q : H.Walk leg.2.1 leg.2.2,
            q.length ≤ C leg.1 leg.2.1 leg.2.2) →
          ∃ q : H.Walk u v,
            q.length ≤ (legs.map fun leg => C leg.1 leg.2.1 leg.2.2).sum := by
  classical
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hpath := p.isPath_of_length_eq_dist hp
  have hchord : ∀ r s : ℕ, r + 1 < s → s ≤ p.length →
      ¬ G.Adj (p.getVert r) (p.getVert s) := by
    intro r s hrs hs hadj
    have hr : r ≤ p.length := by omega
    let q : G.Walk i j := ((p.take r).concat hadj).append (p.drop s)
    have hdist : G.dist i j ≤ q.length := SimpleGraph.dist_le q
    have hqlen : q.length = r + 1 + (p.length - s) := by simp [q, hr]
    rw [← hp, hqlen] at hdist
    omega
  obtain ⟨legs, hlabels, hfits, hroute⟩ :=
    region_walk_deferred_costs S G hoverlap p u hu v hv
  exact ⟨p, hp, hpath, hchord, legs, hlabels,
    hlabels ▸ hpath.support_nodup, hfits, hroute⟩

#print axioms solution
