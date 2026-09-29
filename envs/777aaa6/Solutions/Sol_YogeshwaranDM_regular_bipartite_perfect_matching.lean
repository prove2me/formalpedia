-- Prove2me | solution 1 for YogeshwaranDM.regular_bipartite_perfect_matching
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:52:57.05262+00:00
-- url     : https://prove2.me/submissions/4f2b423c-0752-490f-9a3c-0f76982dae36

import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Tactic

set_option autoImplicit false

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [G.LocallyFinite] (L R : Set V)
    (hG : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ)
    (k : ℕ) (hk : 0 < k) (hreg : ∀ v, G.degree v = k) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  apply G.exists_isPerfectMatching_of_forall_ncard_le hG
  intro S
  let s := S.toFinset
  let t := (⋃ x ∈ S, G.neighborSet x).toFinset
  have hl (x : V) (hx : x ∈ s) : k ≤ (t.bipartiteAbove G.Adj x).card := by
    have he : t.bipartiteAbove G.Adj x = G.neighborFinset x := by
      ext y
      simp only [Finset.mem_bipartiteAbove, SimpleGraph.mem_neighborFinset]
      constructor
      · exact And.right
      · intro hxy
        refine ⟨?_, hxy⟩
        exact Set.mem_toFinset.mpr
          (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨Set.mem_toFinset.mp hx, hxy⟩⟩)
    rw [he, G.card_neighborFinset_eq_degree, hreg]
  have hr (y : V) (_hy : y ∈ t) : (s.bipartiteBelow G.Adj y).card ≤ k := by
    rw [← hreg y, ← G.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro x hx
    exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hx).2.symm
  have hc := Finset.card_nsmul_le_card_nsmul G.Adj hl hr
  have hc' : s.card * k ≤ t.card * k := by simpa only [smul_eq_mul] using hc
  have hc'' := (mul_le_mul_iff_left₀ hk).mp hc'
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  exact hc''
