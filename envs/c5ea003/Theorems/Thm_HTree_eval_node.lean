-- Prove2me | Theorems.Thm_HTree_eval_node
-- name    : HTree.eval_node
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:57.528314+00:00
-- url     : https://prove2.me/theorems/f30a28ef-ed24-43f3-8e87-d33b23749fb7
-- title:
--   Eval node
-- statement:
--   Formal statement of `HTree.eval_node` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HTree.eval_node(L R : HTree α) (s : α → ℝ) :
--       (HTree.node L R).eval s =
--         if s (L.eval s) ≥ s (R.eval s) then L.eval s else R.eval s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/HTreeDefs.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/HTreeDefs.lean#L50

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

theorem HTree.eval_node(L R : HTree α) (s : α → ℝ) :
    (HTree.node L R).eval s =
      if s (L.eval s) ≥ s (R.eval s) then L.eval s else R.eval s := by sorry
