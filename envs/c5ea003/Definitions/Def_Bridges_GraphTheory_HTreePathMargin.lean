-- Prove2me | Definitions.Def_Bridges_GraphTheory_HTreePathMargin
-- name    : Bridges_GraphTheory_HTreePathMargin
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:33.57936+00:00
-- url     : https://prove2.me/theorems/e20b38ca-917e-4379-9bd5-b43bb0121d38
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_HTreePathMargin
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.HTreePathMargin`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/HTreePathMargin.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
import Definitions.Def_Bridges_HTreeRobust
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-!
# Path Margin and Certificate Radius for Elimination Trees

This file defines the `pathMargin` of an elimination tree — the minimum score
margin along the realized winner path — and proves that it provides a valid
certified robustness radius.

## Key insight: tournament winners maximize scores

A crucial structural fact is that the winner of any subtree has the globally
highest score among all leaves in that subtree. This is because at each
comparison, the higher-scoring class advances. Consequently, the pathwise
margin (along the winner path only) is sufficient for robustness.

## Main results

- `HTree.eval_score_ge`: The tournament winner has score ≥ every leaf.
- `HTree.pathMargins`: The list of margins along the realized winner path.
- `HTree.pathMargin_sufficient`: The pathMargin gives a valid robustness
  certificate when combined with a Lipschitz bound.
-/

open Classical

noncomputable section

namespace HTree

variable {α : Type}

/-
The tournament winner has score ≥ every leaf in the subtree.
-/

/-- The list of score margins along the realized winner path. -/
def pathMargins : HTree α → (α → ℝ) → List ℝ
  | .leaf _, _ => []
  | .node L R, s =>
    let u := L.eval s
    let v := R.eval s
    |s u - s v| :: (if s u ≥ s v then L.pathMargins s else R.pathMargins s)

/-
Every element of pathMargins is nonneg (absolute values).
-/

/-
If δ < every margin in pathMargins, then PathDominates holds.
-/

/-
The pathMargin gives a valid robustness certificate.
-/

end HTree

end


