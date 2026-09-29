-- Prove2me | Theorems.Thm_TriangularForest_fan_neighborFinset_of_ne_zero
-- name    : TriangularForest.fan_neighborFinset_of_ne_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:24:19.204041+00:00
-- url     : https://prove2.me/theorems/167a87ac-bdd4-4dc9-a812-c5bc6c1e5859
-- title:
--   Every non-central vertex has exactly the centre and its partner as neighbours.
-- statement:
--   Every non-central vertex has exactly the centre and its partner as neighbours.
--
--   ```lean
--   theorem TriangularForest.fan_neighborFinset_of_ne_zero{k : ℕ} {a : Fin (2 * k + 1)} (ha : a ≠ 0) :
--       (fan k).neighborFinset a = {0, fanPartner a} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TriangularForest/Extremal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TriangularForest/Extremal.lean#L129

-- Thm stub generated from Logic/TriangularForest/Extremal.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Complexity
import Definitions.Def_Logic_TriangularForest_Extremal

/-!
# The sparsity bound is attained for every odd order

`TriangularForest.two_mul_card_edgeFinset_le` says that a triangular forest on `n ≥ 1` vertices
satisfies `2e ≤ 3(n-1)`.  Here we show that this is *sharp for every odd `n`*, by exhibiting the
friendship (windmill) graphs `Fₖ`: `k` triangles glued at a common centre.

* `TriangularForest.isTriangularForest_of_unique_far_neighbour` — a structural membership
  criterion: if every vertex other than a fixed vertex `x` has at most one neighbour besides
  `x`, then the graph is a triangular forest.  This is the "windmill" criterion, and it is proved
  by a rotation argument on cycles rather than by a finite check;
* `TriangularForest.fan` — the friendship graph `Fₖ` on `2k+1` vertices;
* `TriangularForest.isTriangularForest_fan` — `Fₖ` is a triangular forest;
* `TriangularForest.card_edgeFinset_fan` — `Fₖ` has exactly `3k` edges;
* `TriangularForest.sparsity_bound_attained` — hence `2e = 3(n-1)` for `n = 2k+1`: the bound of
  `two_mul_card_edgeFinset_le` cannot be improved for any odd order.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

theorem TriangularForest.fan_neighborFinset_of_ne_zero{k : ℕ} {a : Fin (2 * k + 1)} (ha : a ≠ 0) :
    (fan k).neighborFinset a = {0, fanPartner a} := by sorry
