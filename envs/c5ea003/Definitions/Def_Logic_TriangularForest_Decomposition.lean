-- Prove2me | Definitions.Def_Logic_TriangularForest_Decomposition
-- name    : Logic_TriangularForest_Decomposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:12:07.019701+00:00
-- url     : https://prove2.me/theorems/f20ff665-9d47-4865-a778-0fc92df68902
-- title:
--   Aether Catalog definitions — Logic_TriangularForest_Decomposition
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TriangularForest.Decomposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TriangularForest/Decomposition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_TriangularForest_Defs

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

namespace TriangularForest

open SimpleGraph Finset

variable {V : Type*}

/-- `G` **decomposes into two triangular forests** when its edges can be split into two
edge-disjoint triangular forests. -/
def DecomposesIntoTwo (G : SimpleGraph V) : Prop :=
  ∃ G₁ G₂ : SimpleGraph V, IsTriangularForest G₁ ∧ IsTriangularForest G₂ ∧
    Disjoint G₁ G₂ ∧ G₁ ⊔ G₂ = G

section Counting

variable [Fintype V] [DecidableEq V]



end Counting

section CompleteGraphs



end CompleteGraphs

section Thickness

variable [Fintype V] [DecidableEq V]




end Thickness

section Example

/-- The first half of an explicit decomposition of `K₅`: the triangle `0-1-2` with the pendant
edges `0-4` and `1-3`. -/
def K5part1 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ [((0 : Fin 5), (1 : Fin 5)), (0, 2), (0, 4), (1, 2), (1, 3)]

/-- The second half of an explicit decomposition of `K₅`: the triangle `2-3-4` with the pendant
edges `0-3` and `1-4`. -/
def K5part2 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun a b => (a, b) ∈ [((0 : Fin 5), (3 : Fin 5)), (1, 4), (2, 3), (2, 4), (3, 4)]

instance : DecidableRel K5part1.Adj :=
  inferInstanceAs (DecidableRel fun a b : Fin 5 => a ≠ b ∧
    ((a, b) ∈ [((0 : Fin 5), (1 : Fin 5)), (0, 2), (0, 4), (1, 2), (1, 3)] ∨
     (b, a) ∈ [((0 : Fin 5), (1 : Fin 5)), (0, 2), (0, 4), (1, 2), (1, 3)]))

instance : DecidableRel K5part2.Adj :=
  inferInstanceAs (DecidableRel fun a b : Fin 5 => a ≠ b ∧
    ((a, b) ∈ [((0 : Fin 5), (3 : Fin 5)), (1, 4), (2, 3), (2, 4), (3, 4)] ∨
     (b, a) ∈ [((0 : Fin 5), (3 : Fin 5)), (1, 4), (2, 3), (2, 4), (3, 4)]))




end Example

end TriangularForest


