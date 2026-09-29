-- Prove2me | solution 1 for HTree.eval_mem_classes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:36.307158+00:00
-- url     : https://prove2.me/submissions/b7545d36-1fdb-47fb-84e8-3ea1a7ff3683

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
theorem solution[DecidableEq α] (T : HTree α) (s : α → ℝ) :
    T.eval s ∈ T.classes := by
  induction T with
  | leaf a => simp [eval, classes]
  | node L R ihL ihR =>
    simp only [HTree.eval, HTree.classes, Finset.mem_union]
    split
    · exact Or.inl ihL
    · exact Or.inr ihR
