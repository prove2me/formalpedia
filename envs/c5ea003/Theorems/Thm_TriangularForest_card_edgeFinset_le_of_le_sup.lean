-- Prove2me | Theorems.Thm_TriangularForest_card_edgeFinset_le_of_le_sup
-- name    : TriangularForest.card_edgeFinset_le_of_le_sup
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:58:01.406683+00:00
-- url     : https://prove2.me/theorems/bb9405b2-2a0b-4427-8703-c5cb8da1937c
-- title:
--   The edges of a graph covered by two graphs are covered by their edges.
-- statement:
--   The edges of a graph covered by two graphs are covered by their edges.
--
--   ```lean
--   theorem TriangularForest.card_edgeFinset_le_of_le_sup{G G₁ G₂ : SimpleGraph V} [DecidableRel G.Adj]
--       [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : G ≤ G₁ ⊔ G₂) :
--       #G.edgeFinset ≤ #G₁.edgeFinset + #G₂.edgeFinset := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Decomposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Decomposition.lean#L39

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

theorem TriangularForest.card_edgeFinset_le_of_le_sup{G G₁ G₂ : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] (h : G ≤ G₁ ⊔ G₂) :
    #G.edgeFinset ≤ #G₁.edgeFinset + #G₂.edgeFinset := by sorry
