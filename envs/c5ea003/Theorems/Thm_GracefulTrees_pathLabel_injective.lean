-- Prove2me | Theorems.Thm_GracefulTrees_pathLabel_injective
-- name    : GracefulTrees.pathLabel_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:58.657358+00:00
-- url     : https://prove2.me/theorems/48a87e49-73b2-4454-9b04-23cef653623b
-- title:
--   The alternating path labeling is injective.
-- statement:
--   The alternating path labeling is injective.
--
--   ```lean
--   theorem GracefulTrees.pathLabel_injective(n : ℕ) : Function.Injective (pathLabel n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/GracefulTrees.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/GracefulTrees.lean#L36

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

theorem GracefulTrees.pathLabel_injective(n : ℕ) : Function.Injective (pathLabel n) := by sorry
