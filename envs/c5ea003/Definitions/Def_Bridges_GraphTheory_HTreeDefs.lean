-- Prove2me | Definitions.Def_Bridges_GraphTheory_HTreeDefs
-- name    : Bridges_GraphTheory_HTreeDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:32.313512+00:00
-- url     : https://prove2.me/theorems/8bb83885-0746-418d-9703-c2f28939ab13
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_HTreeDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.HTreeDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/HTreeDefs.lean by skeleton subtraction
import Mathlib
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

/-- Binary elimination tree with leaves labeled by elements of `α`.
    Internal nodes represent pairwise comparisons: the winners of the left
    and right subtrees are compared, and the higher-scoring one advances. -/
inductive HTree (α : Type)
  | leaf : α → HTree α
  | node : HTree α → HTree α → HTree α
  deriving DecidableEq

namespace HTree

variable {α : Type}

/-- The winner of the elimination tournament using score function `s`.
    At each internal node, the winners of the left and right subtrees
    are compared, and the one with the higher (or equal) score advances. -/
def eval : HTree α → (α → ℝ) → α
  | .leaf a, _ => a
  | .node L R, s =>
    let u := L.eval s
    let v := R.eval s
    if s u ≥ s v then u else v



/-- The set of class labels appearing as leaves in the subtree. -/
def classes [DecidableEq α] : HTree α → Finset α
  | .leaf a => {a}
  | .node L R => L.classes ∪ R.classes





end HTree

end


