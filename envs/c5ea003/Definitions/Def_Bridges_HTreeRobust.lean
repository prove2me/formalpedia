-- Prove2me | Definitions.Def_Bridges_HTreeRobust
-- name    : Bridges_HTreeRobust
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:03.27883+00:00
-- url     : https://prove2.me/theorems/bd406380-d768-4f64-86b5-f873d081cb6e
-- title:
--   Aether Catalog definitions — Bridges_HTreeRobust
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HTreeRobust`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HTreeRobust.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Hierarchical Classifier Robustness via Tournament Margin Decomposition

This file proves certified robustness theorems for hierarchical multiclass
classifiers built from pairwise score comparisons in a binary elimination tree.

## Main results

### Atomic comparison stability
- `ge_iff_of_abs_sub_lt`: If two differences have perturbation less than the
  absolute gap, the comparison direction is preserved.

### Global margin robustness
- `HTree.AllMarginsAbove`: Predicate that every internal node has margin > δ.
- `HTree.eval_stable`: The tournament winner is preserved if all margins exceed
  the perturbation bound.
- `HTree.eval_stable_of_lip`: Lipschitz-parameterized version.

### Pathwise domination robustness (sharper certificate)
- `HTree.PathDominates`: At each node on the winner path, the winner's score
  exceeds ALL classes in the losing subtree by more than δ.
- `HTree.eval_stable_of_pathDom`: The tournament winner is preserved under
  the pathwise domination condition. This is strictly sharper than the global
  margin certificate because it only requires margins along the realized path.

## Key insight

The pathwise certificate `PathDominates` is genuinely sharper than `AllMarginsAbove`
because it does not require stability of comparisons in subtrees that are never
reached by the winner. However, at each node on the winner path, the domination
condition must be against ALL classes in the losing subtree (not just the subtree
winner), because the losing subtree's tournament winner can change under perturbation.
-/

open Classical

noncomputable section

/-! ### Atomic comparison stability -/

/-
If two differences have perturbation bounded by `δ` and the original gap
    exceeds `δ`, then the comparison direction is preserved.
    This is the atomic robustness step for pairwise score comparisons.
-/

/-
Variant: if the score difference perturbation is bounded and the gap is
    positive, the sign of the difference is preserved.
-/

/-
If `δ < a - b` and `|(a - b) - (a' - b')| ≤ δ`, then `a' > b'`.
-/

namespace HTree

variable {α : Type} {X : Type}

/-! ### Global margin robustness -/

/-- Recursive predicate: every internal node of the tree has absolute score margin
    strictly exceeding `δ`. This descends into BOTH children at each node. -/
def AllMarginsAbove : HTree α → (α → ℝ) → ℝ → Prop
  | .leaf _, _, _ => True
  | .node L R, s, δ =>
    δ < |s (L.eval s) - s (R.eval s)| ∧
    L.AllMarginsAbove s δ ∧
    R.AllMarginsAbove s δ



/-
**Global margin robustness theorem**: If every internal node has margin exceeding
    the perturbation bound `δ`, and score differences are perturbed by at most `δ`,
    then the tournament winner is unchanged.

    The proof proceeds by induction on the tree structure. At each node, the
    induction hypothesis guarantees both children produce the same winners,
    and the gap condition ensures the root comparison is preserved.
-/

/-
**Lipschitz version**: robustness under a global Lipschitz condition on
    score differences and a distance bound.
-/

/-! ### Pathwise domination robustness (sharper certificate) -/

/-- **Pathwise domination predicate**: At each node on the winner path, the winner's
    score exceeds ALL class labels in the losing subtree by more than `δ`.

    This is sharper than `AllMarginsAbove` because:
    1. It only constrains nodes on the realized winner path.
    2. At each such node, the margin condition is against the subtree winner,
       but to ensure correctness when the losing subtree's winner changes under
       perturbation, we require domination over ALL classes in the losing subtree. -/
def PathDominates [DecidableEq α] : HTree α → (α → ℝ) → ℝ → Prop
  | .leaf _, _, _ => True
  | .node L R, s, δ =>
    let u := L.eval s
    let v := R.eval s
    if s u ≥ s v then
      (∀ c ∈ R.classes, δ < s u - s c) ∧ L.PathDominates s δ
    else
      (∀ c ∈ L.classes, δ < s v - s c) ∧ R.PathDominates s δ

/-
**Pathwise domination robustness theorem**: If the winner at each node on
    the realized path dominates all classes in the losing subtree by more than
    the perturbation bound, the tournament winner is preserved.

    This gives a strictly sharper certificate than `eval_stable` because it does
    not require any margins from comparisons in subtrees that the winner never
    visits. The key structural insight is that the losing subtree's internal
    tournament outcome is irrelevant — only the winning subtree needs recursive
    stability.
-/

/-
`AllMarginsAbove` implies `PathDominates`: the global condition is stronger.
-/

/-! ### Certified radius -/

/-
The certified robustness radius: the minimum score margin across all internal
    nodes divided by the Lipschitz constant. Within this radius, the tournament
    winner is guaranteed to be preserved.
-/

end HTree

end


