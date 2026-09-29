-- Prove2me | Theorems.Thm_TriangularForest_four_mul_lt_choose_two_add_six
-- name    : TriangularForest.four_mul_lt_choose_two_add_six
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:59:16.944683+00:00
-- url     : https://prove2.me/theorems/d88317dd-bef6-4c4d-8b90-ff84af7cba22
-- title:
--   Arithmetic core of the obstruction: for `n ≥ 8` the complete graph has more than `4n - 6`
-- statement:
--   Arithmetic core of the obstruction: for `n ≥ 8` the complete graph has more than `4n - 6`
--   edges.
--
--   ```lean
--   theorem TriangularForest.four_mul_lt_choose_two_add_six{n : ℕ} (hn : 8 ≤ n) : 4 * n < n.choose 2 + 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Decomposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Decomposition.lean#L69

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

theorem TriangularForest.four_mul_lt_choose_two_add_six{n : ℕ} (hn : 8 ≤ n) : 4 * n < n.choose 2 + 6 := by sorry
