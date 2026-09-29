-- Prove2me | Theorems.Thm_GracefulTrees_starGraph_isGraceful
-- name    : GracefulTrees.starGraph_isGraceful
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:34:27.913444+00:00
-- url     : https://prove2.me/theorems/3387598d-6cc6-4d72-a769-5e7d98a2e5f4
-- title:
--   Every star `K_{1,n}` is graceful.
-- statement:
--   Every star `K_{1,n}` is graceful.
--
--   ```lean
--   theorem GracefulTrees.starGraph_isGraceful(n : ℕ) :
--       IsGraceful (completeBipartiteGraph Unit (Fin n)) n (starLabel n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulStars.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulStars.lean#L38

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

theorem GracefulTrees.starGraph_isGraceful(n : ℕ) :
    IsGraceful (completeBipartiteGraph Unit (Fin n)) n (starLabel n) := by sorry
