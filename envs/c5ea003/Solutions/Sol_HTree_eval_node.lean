-- Prove2me | solution 1 for HTree.eval_node
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:46:38.403681+00:00
-- url     : https://prove2.me/submissions/117aa894-d8d9-40a5-9dcc-81483966af33

-- Sol generated from Bridges/GraphTheory/HTreeDefs.lean
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











open HTree in
theorem solution(L R : HTree α) (s : α → ℝ) :
    (HTree.node L R).eval s =
      if s (L.eval s) ≥ s (R.eval s) then L.eval s else R.eval s := rfl
