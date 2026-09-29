-- Prove2me | Theorems.Thm_HTree_eval_mem_classes
-- name    : HTree.eval_mem_classes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:45.599311+00:00
-- url     : https://prove2.me/theorems/59e41546-1c61-4375-af3b-f652b58ce230
-- title:
--   The winner of the elimination tournament is always a leaf of the tree.
-- statement:
--   The winner of the elimination tournament is always a leaf of the tree.
--
--   ```lean
--   theorem HTree.eval_mem_classes[DecidableEq α] (T : HTree α) (s : α → ℝ) :
--       T.eval s ∈ T.classes := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/HTreeDefs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/HTreeDefs.lean#L66

-- Thm stub generated from Bridges/GraphTheory/HTreeDefs.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Binary Elimination Trees: Definitions

This file defines binary elimination trees (`HTree`) and their core operations,
forming the foundation for hierarchical classifier robustness theory.

## Main definitions

- `HTree α`: A binary tree with leaves labeled by elements of `α`.
- `HTree.eval`: The winner of the elimination tournament under a score function.
- `HTree.classes`: The set of class labels appearing as leaves.
- `HTree.eval_mem_classes`: The winner is always a leaf of the tree.
- `HTree.depth`: The depth of the tree.
-/

open Classical

noncomputable section


open HTree

variable {α : Type}

theorem HTree.eval_mem_classes[DecidableEq α] (T : HTree α) (s : α → ℝ) :
    T.eval s ∈ T.classes := by sorry
