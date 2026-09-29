-- Prove2me | Definitions.Def_Logic_TriangularForest_ClassProperties
-- name    : Logic_TriangularForest_ClassProperties
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:20:43.678738+00:00
-- url     : https://prove2.me/theorems/1efcedc4-152e-40da-a742-7ddf4212bb65
-- title:
--   Aether Catalog definitions — Logic_TriangularForest_ClassProperties
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TriangularForest.ClassProperties`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TriangularForest/ClassProperties.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_length_le_card_two_le_degree_of_isCycle

/-!
# The class of triangular forests as a graph class

Lee, Liu and Tsai study edge-decomposition into `k` members of a graph class `F` which is closed
under topological minors and 1-sums, has decidable membership, contains a triangle, and is not
the class of all graphs.  Triangular forests are the smallest interesting such class.  This file
verifies the elementary side of those requirements for triangular forests and records the local
structure they force:

* `TriangularForest.instDecidableIsCycle`, `TriangularForest.instDecidableIsTriangularForest` —
  membership in the class is decidable for finite graphs (cycles are bounded in length by the
  number of vertices, so a finite search suffices);
* `TriangularForest.triangle_isTriangularForest` — the class contains a triangle;
* `TriangularForest.not_isTriangularForest_completeGraph_four` — `K₄` is not a triangular forest,
  so the class is not the class of all graphs;
* `IsTriangularForest.mono` (in `Defs`) — closure under subgraphs;
* `TriangularForest.no_four_cycle` — triangular forests are `C₄`-free, and hence
  `TriangularForest.neighborhood_matching`: the neighbourhood of any vertex induces a matching,
  so every edge lies in at most one triangle;
* `TriangularForest.triangle_tight` — the sparsity bound `2e ≤ 3(n-1)` is attained (by a
  triangle), so it cannot be improved.
-/

namespace TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

section Decidability

/-- Being a cycle is a decidable property of a closed walk. -/
instance instDecidableIsCycle [DecidableEq V] {v : V} (c : G.Walk v v) : Decidable c.IsCycle :=
  decidable_of_iff (c.edges.Nodup ∧ ¬ c.Nil ∧ c.support.tail.Nodup) (by
    rw [Walk.isCycle_def, Walk.isTrail_def]
    exact ⟨fun h => ⟨h.1, fun hcc => h.2.1 (Walk.eq_nil_iff_nil.mp hcc), h.2.2⟩,
      fun h => ⟨h.1, fun hcc => h.2.1 (Walk.eq_nil_iff_nil.mpr hcc), h.2.2⟩⟩)

/-- Cycles are shorter than `|V| + 1`, so being a triangular forest is a finite search. -/
theorem isTriangularForest_iff_forall_short [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    IsTriangularForest G ↔
      ∀ v : V, ∀ c ∈ G.finsetWalkLengthLT (Fintype.card V + 1) v v, c.IsCycle → c.length = 3 := by
  constructor
  · intro h v c _ hc
    exact h c hc
  · intro h v c hc
    refine h v c ?_ hc
    rw [SimpleGraph.mem_finsetWalkLengthLT_iff]
    have h1 := length_le_card_two_le_degree_of_isCycle hc
    have h2 : #{x ∈ (univ : Finset V) | 2 ≤ G.degree x} ≤ Fintype.card V :=
      le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_univ))
    omega

/-- **Membership in the class of triangular forests is decidable.** -/
instance instDecidableIsTriangularForest [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Decidable (IsTriangularForest G) :=
  decidable_of_iff _ isTriangularForest_iff_forall_short.symm

end Decidability

section Examples




end Examples

section LocalStructure




end LocalStructure

end TriangularForest


