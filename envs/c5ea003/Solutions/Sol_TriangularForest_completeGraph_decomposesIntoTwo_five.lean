-- Prove2me | solution 1 for TriangularForest.completeGraph_decomposesIntoTwo_five
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:44:59.195217+00:00
-- url     : https://prove2.me/submissions/608ccddd-27ed-4678-b823-a83d9a923062

-- Sol generated from Logic/TriangularForest/Decomposition.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_isTriangularForest_of_card_two_le_degree_le_three

/-!
# Edge decompositions into triangular forests

The paper *Edge-decomposition into Two Triangular Forests is NP-complete* studies the decision
problem: given `G`, can `E(G)` be partitioned into two triangular forests?  This file develops
the *extremal* side of that problem, which is what constrains any such decomposition:

* `TriangularForest.DecomposesIntoTwo` — the decision predicate (an edge-disjoint cover by two
  triangular forests);
* `TriangularForest.card_edgeFinset_add_six_le_of_decomposesIntoTwo` — a decomposable graph on
  `n ≥ 2` vertices has at most `4n - 6` edges;
* `TriangularForest.completeGraph_not_decomposesIntoTwo` — consequently `Kₙ` is **not**
  decomposable into two triangular forests for `n ≥ 8`;
* `TriangularForest.completeGraph_decomposesIntoTwo_five` — by contrast `K₅` *is* decomposable,
  an explicit certificate (a triangle with two pendant edges, twice);
* `TriangularForest.card_choose_two_le_of_cover` and
  `TriangularForest.triangularThickness_lower_bound` — the `k`-fold generalisation: covering
  `Kₙ` by `k` triangular forests forces `k ≥ (n-1)/4`, so the "triangular thickness" of `Kₙ`
  grows linearly in `n`.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*}



variable [Fintype V] [DecidableEq V]









variable [Fintype V] [DecidableEq V]










theorem K5part1_isTriangularForest : IsTriangularForest K5part1 :=
  isTriangularForest_of_card_two_le_degree_le_three (by decide)

theorem K5part2_isTriangularForest : IsTriangularForest K5part2 :=
  isTriangularForest_of_card_two_le_degree_le_three (by decide)




open TriangularForest in
theorem solution:
    DecomposesIntoTwo (⊤ : SimpleGraph (Fin 5)) := by
  refine ⟨K5part1, K5part2, K5part1_isTriangularForest, K5part2_isTriangularForest, ?_, ?_⟩
  · rw [disjoint_iff]
    ext a b
    revert a b
    decide
  · ext a b
    revert a b
    decide
