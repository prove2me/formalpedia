-- Prove2me | Theorems.Thm_TriangularForest_DecomposesIntoTwo_comap
-- name    : TriangularForest.DecomposesIntoTwo.comap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:23:59.318674+00:00
-- url     : https://prove2.me/theorems/0d3596bb-3738-43b2-b101-c9c9fd9b0a7b
-- title:
--   Decomposability into two triangular forests is inherited by pullbacks along injections.
-- statement:
--   Decomposability into two triangular forests is inherited by pullbacks along injections.
--
--   ```lean
--   theorem TriangularForest.DecomposesIntoTwo.comap{H : SimpleGraph W} (f : W ↪ V) (hG : DecomposesIntoTwo G)
--       (hH : H ≤ G.comap f) : DecomposesIntoTwo H := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/CliqueObstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/CliqueObstruction.lean#L33

-- Thm stub generated from Logic/TriangularForest/CliqueObstruction.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_ClassProperties
import Definitions.Def_Logic_TriangularForest_Decomposition

/-!
# A clique obstruction to decomposing into two triangular forests

The sharp threshold `Kₙ` (decomposable iff `n ≤ 5`) upgrades to an obstruction for *arbitrary*
graphs: since the property of decomposing into two triangular forests is inherited by subgraphs
(pulled back along injections), any graph containing six mutually adjacent vertices fails to
decompose.

* `TriangularForest.IsTriangularForest.comap` — triangular forests pull back along injections;
* `TriangularForest.DecomposesIntoTwo.comap` — so does decomposability, whenever the pullback
  of the ambient graph is the graph we decompose;
* `TriangularForest.not_decomposesIntoTwo_of_six_clique` — a graph with a `K₆` subgraph does not
  decompose into two triangular forests.
-/

open TriangularForest

open SimpleGraph Finset

variable {V W : Type*} {G : SimpleGraph V}

theorem TriangularForest.DecomposesIntoTwo.comap{H : SimpleGraph W} (f : W ↪ V) (hG : DecomposesIntoTwo G)
    (hH : H ≤ G.comap f) : DecomposesIntoTwo H := by sorry
