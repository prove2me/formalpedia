-- Prove2me | Theorems.Thm_GracefulTrees_pathGraph_isGraceful
-- name    : GracefulTrees.pathGraph_isGraceful
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:52.146802+00:00
-- url     : https://prove2.me/theorems/bcd13362-65c1-4f26-9ba5-6d210801490d
-- title:
--   The standard alternating labeling is graceful on Mathlib's path graph.
-- statement:
--   The standard alternating labeling is graceful on Mathlib's path graph.
--
--   ```lean
--   theorem GracefulTrees.pathGraph_isGraceful(n : ℕ) :
--       IsGraceful (pathGraph (n + 1)) n (pathLabel n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulTrees.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulTrees.lean#L72

-- Thm stub generated from Algebra/GracefulTrees.lean
import Mathlib
import Definitions.Def_Algebra_GracefulTrees

/-!
# Graceful labelings of paths and their decomposition connection

The Graceful Tree Conjecture is open.  This file formalizes the standard notion and proves
an infinite established case: every finite path is graceful.  It also proves the elementary
counting theorem used when graceful copies partition the edges of a complete graph.
-/

open Finset SimpleGraph

open GracefulTrees

theorem GracefulTrees.pathGraph_isGraceful(n : ℕ) :
    IsGraceful (pathGraph (n + 1)) n (pathLabel n) := by sorry
