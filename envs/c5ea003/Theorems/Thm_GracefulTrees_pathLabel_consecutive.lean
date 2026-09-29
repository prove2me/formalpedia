-- Prove2me | Theorems.Thm_GracefulTrees_pathLabel_consecutive
-- name    : GracefulTrees.pathLabel_consecutive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:44.905928+00:00
-- url     : https://prove2.me/theorems/12457f8a-11cb-46cf-b3b0-bcdcff282d3f
-- title:
--   Consecutive labels have differences `n,n-1,…,1`.
-- statement:
--   Consecutive labels have differences `n,n-1,…,1`.
--
--   ```lean
--   theorem GracefulTrees.pathLabel_consecutive(n : ℕ) (i : Fin (n + 1)) (hi : i.1 + 1 < n + 1) :
--       Nat.dist (pathLabel n i) (pathLabel n ⟨i.1 + 1, hi⟩) = n - i.1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulTrees.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulTrees.lean#L52

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

theorem GracefulTrees.pathLabel_consecutive(n : ℕ) (i : Fin (n + 1)) (hi : i.1 + 1 < n + 1) :
    Nat.dist (pathLabel n i) (pathLabel n ⟨i.1 + 1, hi⟩) = n - i.1 := by sorry
