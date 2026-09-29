-- Prove2me | Definitions.Def_Bridges_GraphTheory_LHTreeRobust
-- name    : Bridges_GraphTheory_LHTreeRobust
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:46.445751+00:00
-- url     : https://prove2.me/theorems/2437b0e1-b4e7-4ee7-abeb-adac0a06eeb4
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_LHTreeRobust
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.LHTreeRobust`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/LHTreeRobust.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_HTreeRobust
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-!
# Heterogeneous Lipschitz Robustness for Labeled Elimination Trees

This file extends the hierarchical robustness theory to elimination trees where
each internal node has its own Lipschitz constant.

## Main results

- `LHTree.eval_stable`: The tournament winner is preserved if each node's
  margin exceeds its own perturbation budget.
-/

open Classical

noncomputable section

/-- Binary elimination tree with per-node Lipschitz constants. -/
inductive LHTree (α : Type)
  | leaf : α → LHTree α
  | node : ℝ → LHTree α → LHTree α → LHTree α

namespace LHTree

variable {α : Type} {X : Type}

/-- Winner of the labeled elimination tournament. -/
def eval : LHTree α → (α → ℝ) → α
  | .leaf a, _ => a
  | .node _ L R, s =>
    let u := L.eval s
    let v := R.eval s
    if s u ≥ s v then u else v



/-- Nodewise Lipschitz condition with nonneg constants. -/
def NodewiseLip : LHTree α → (α → X → ℝ) → (X → X → ℝ) → Prop
  | .leaf _, _, _ => True
  | .node c L R, score, D =>
    (0 ≤ c) ∧
    (∀ u v x y,
      |(score u x - score v x) - (score u y - score v y)| ≤ c * D x y) ∧
    L.NodewiseLip score D ∧
    R.NodewiseLip score D

/-- Per-node margin condition. -/
def NodeMarginsAbove : LHTree α → (α → ℝ) → ℝ → Prop
  | .leaf _, _, _ => True
  | .node c L R, s, r =>
    c * r < |s (L.eval s) - s (R.eval s)| ∧
    L.NodeMarginsAbove s r ∧
    R.NodeMarginsAbove s r

/-
**Heterogeneous robustness theorem**: If each internal node's margin
    exceeds its own Lipschitz constant times the distance bound, and the
    nodewise Lipschitz condition holds, then the tournament winner is preserved.
-/

end LHTree

end


