-- Prove2me | Theorems.Thm_TriangularForest_card_edgeFinset_le_sum_of_cover
-- name    : TriangularForest.card_edgeFinset_le_sum_of_cover
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:57:54.074346+00:00
-- url     : https://prove2.me/theorems/fad088eb-db4c-400e-a0d4-d4121c7cbb32
-- title:
--   If the edges of `G` are covered by a family of `k` graphs, its edge count is at most the sum
-- statement:
--   If the edges of `G` are covered by a family of `k` graphs, its edge count is at most the sum
--   of theirs.
--
--   ```lean
--   theorem TriangularForest.card_edgeFinset_le_sum_of_cover{k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
--       (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj]
--       (hcov : ∀ x y : V, G.Adj x y → ∃ i, (H i).Adj x y) :
--       #G.edgeFinset ≤ ∑ i, #(H i).edgeFinset := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Decomposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Decomposition.lean#L105

-- Thm stub generated from Logic/TriangularForest/Decomposition.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition

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

theorem TriangularForest.card_edgeFinset_le_sum_of_cover{k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Fin k → SimpleGraph V) [∀ i, DecidableRel (H i).Adj]
    (hcov : ∀ x y : V, G.Adj x y → ∃ i, (H i).Adj x y) :
    #G.edgeFinset ≤ ∑ i, #(H i).edgeFinset := by sorry
