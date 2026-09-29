-- Prove2me | solution 1 for TriangularForest.edges_side
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:54:33.18913+00:00
-- url     : https://prove2.me/submissions/6a370e0c-c89c-47b3-930b-1193cdf4ab82

-- Sol generated from Logic/TriangularForest/OneSum.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties

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
    {u w : V} (p : (G₁ ⊔ G₂).Walk u w) (hne : ∀ i < p.length, p.getVert i ≠ x) :
    (∀ e ∈ p.edges, e ∈ G₁.edgeSet) ∨ (∀ e ∈ p.edges, e ∈ G₂.edgeSet) := by
  induction p with
  | nil => exact Or.inl (by simp)
  | @cons a b c h q ih =>
    have hne' : ∀ i < q.length, q.getVert i ≠ x := by
      intro i hi
      have := hne (i + 1) (by simp only [Walk.length_cons]; omega)
      simpa using this
    cases q with
    | nil =>
      rcases ((sup_adj _ _ _ _).1 h) with h1 | h1
      · exact Or.inl (by simp [h1])
      · exact Or.inr (by simp [h1])
    | @cons _ c' _ h' q' =>
      have hbx : b ≠ x := by
        have := hne' 0 (by simp only [Walk.length_cons]; omega)
        simpa using this
      rcases ih hne' with hL | hR
      · have hb' : G₁.Adj b c' := by
          have : s(b, c') ∈ (Walk.cons h' q').edges := by simp
          simpa using hL _ this
        rcases ((sup_adj _ _ _ _).1 h) with h1 | h1
        · refine Or.inl ?_
          intro e he
          rw [Walk.edges_cons, List.mem_cons] at he
          rcases he with rfl | he
          · simpa using h1
          · exact hL _ he
        · exact absurd (hx b ⟨c', hb'⟩ ⟨a, h1.symm⟩) hbx
      · have hb' : G₂.Adj b c' := by
          have : s(b, c') ∈ (Walk.cons h' q').edges := by simp
          simpa using hR _ this
        rcases ((sup_adj _ _ _ _).1 h) with h1 | h1
        · exact absurd (hx b ⟨a, h1.symm⟩ ⟨c', hb'⟩) hbx
        · refine Or.inr ?_
          intro e he
          rw [Walk.edges_cons, List.mem_cons] at he
          rcases he with rfl | he
          · simpa using h1
          · exact hR _ he
