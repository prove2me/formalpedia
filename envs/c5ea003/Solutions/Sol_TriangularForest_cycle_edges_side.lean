-- Prove2me | solution 1 for TriangularForest.cycle_edges_side
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:56:18.332485+00:00
-- url     : https://prove2.me/submissions/7d144338-7ad7-466a-afac-53e592ca8b9e

-- Sol generated from Logic/TriangularForest/OneSum.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties
import Theorems.Thm_TriangularForest_edges_side

/-!
# Triangular forests are closed under 1-sums

A *1-sum* of two graphs glues them along a single vertex.  Together with closure under
subgraphs, decidable membership, containing a triangle and not being everything, this is one of
the properties the Lee–Liu–Tsai framework requires of the graph class `F`.

The formalisation keeps both summands on the same vertex type: `G₁` and `G₂` are graphs whose
supports meet in at most one vertex `x`, and the 1-sum is `G₁ ⊔ G₂`.

The combinatorial core is `TriangularForest.edges_side`: along a walk that avoids `x` at every
position except possibly its last, consecutive edges are forced to stay on the same side, since
a vertex incident to an edge of `G₁` and to an edge of `G₂` must be the gluing vertex `x`.  A
cycle can then be transferred wholesale into `G₁` or into `G₂`, where it is a triangle.
-/

open TriangularForest

open SimpleGraph

variable {V : Type*} {G₁ G₂ : SimpleGraph V} {x : V}





open TriangularForest in
theorem solution(hx : ∀ y : V, (∃ u, G₁.Adj y u) → (∃ w, G₂.Adj y w) → y = x)
    {v : V} (c : (G₁ ⊔ G₂).Walk v v) (hc : c.IsCycle) :
    ∃ (u : V) (c' : (G₁ ⊔ G₂).Walk u u), c'.IsCycle ∧ c'.length = c.length ∧
      ((∀ e ∈ c'.edges, e ∈ G₁.edgeSet) ∨ (∀ e ∈ c'.edges, e ∈ G₂.edgeSet)) := by
  classical
  by_cases hxs : x ∈ c.support
  · -- rotate the cycle so that it starts at the gluing vertex
    refine ⟨x, c.rotate x hxs, (Walk.isCycle_rotate hxs).2 hc, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := c.rotate_edges x hxs
      have hlen : (c.rotate x hxs).edges.length = c.edges.length := by
        rw [← hn, List.length_rotate]
      simpa [Walk.length_edges] using hlen
    · set c' := c.rotate x hxs with hc'def
      have hc' : c'.IsCycle := (Walk.isCycle_rotate hxs).2 hc
      have hlen : 3 ≤ c'.length := hc'.three_le_length
      obtain ⟨y, h₀, q, hq⟩ := Walk.not_nil_iff.1 hc'.not_nil
      have hqlen : q.length = c'.length - 1 := by
        have : c'.length = q.length + 1 := by rw [hq]; simp
        omega
      -- interior vertices of the cycle differ from `x`
      have hinner : ∀ i < q.length, q.getVert i ≠ x := by
        intro i hi hcon
        have hgv : c'.getVert (i + 1) = x := by
          rw [hq]
          simpa using hcon
        have hle : i + 1 ≤ c'.length := by omega
        have := (hc'.getVert_endpoint_iff hle).1 hgv
        omega
      have hyx : y ≠ x := by
        have h0 : q.getVert 0 = y := by simp
        have := hinner 0 (by omega)
        rw [h0] at this
        exact this
      have hqnil : ¬ q.Nil := Walk.not_nil_iff_lt_length.2 (by omega)
      obtain ⟨z, hyz, q', hq'⟩ := Walk.not_nil_iff.1 hqnil
      rcases edges_side hx q hinner with hL | hR
      · refine Or.inl ?_
        have hyz₁ : G₁.Adj y z := by
          have : s(y, z) ∈ q.edges := by rw [hq']; simp
          simpa using hL _ this
        have h₀₁ : G₁.Adj x y := by
          rcases ((sup_adj _ _ _ _).1 h₀) with h1 | h1
          · exact h1
          · exact absurd (hx y ⟨z, hyz₁⟩ ⟨x, h1.symm⟩) hyx
        intro e he
        rw [hq, Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he
        · simpa using h₀₁
        · exact hL _ he
      · refine Or.inr ?_
        have hyz₂ : G₂.Adj y z := by
          have : s(y, z) ∈ q.edges := by rw [hq']; simp
          simpa using hR _ this
        have h₀₂ : G₂.Adj x y := by
          rcases ((sup_adj _ _ _ _).1 h₀) with h1 | h1
          · exact absurd (hx y ⟨x, h1.symm⟩ ⟨z, hyz₂⟩) hyx
          · exact h1
        intro e he
        rw [hq, Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he
        · simpa using h₀₂
        · exact hR _ he
  · refine ⟨v, c, hc, rfl, edges_side hx c ?_⟩
    intro i _ hcon
    exact hxs (hcon ▸ c.getVert_mem_support i)
