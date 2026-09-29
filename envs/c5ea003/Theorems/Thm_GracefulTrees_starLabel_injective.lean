-- Prove2me | Theorems.Thm_GracefulTrees_starLabel_injective
-- name    : GracefulTrees.starLabel_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:34:18.989206+00:00
-- url     : https://prove2.me/theorems/f18eecfd-0a71-437c-8154-9f8f2ef74e5d
-- title:
--   The centre-and-leaves labeling is injective.
-- statement:
--   The centre-and-leaves labeling is injective.
--
--   ```lean
--   theorem GracefulTrees.starLabel_injective(n : ℕ) : Function.Injective (starLabel n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulStars.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulStars.lean#L19

-- Thm stub generated from Algebra/GracefulStars.lean
import Mathlib
import Definitions.Def_Algebra_GracefulStars
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of stars

Stars form a basic infinite family of caterpillars.  This file proves directly that the
complete bipartite graph `K_{1,n}` is graceful.
-/

open Finset SimpleGraph
open GracefulTrees

open GracefulTrees

theorem GracefulTrees.starLabel_injective(n : ℕ) : Function.Injective (starLabel n) := by sorry
