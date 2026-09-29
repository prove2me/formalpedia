-- Prove2me | solution 1 for HTree.eval_stable_of_pathDom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:11:11.492375+00:00
-- url     : https://prove2.me/submissions/8f23ae56-cbd9-46c6-a0d8-a83e012c8527

-- Sol generated from Bridges/HTreeRobust.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
import Definitions.Def_Bridges_HTreeRobust
import Theorems.Thm_HTree_eval_mem_classes
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

open HTree

variable {α : Type} {X : Type}

/-! ### Global margin robustness -/




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



open HTree in
theorem solution[DecidableEq α]
    (T : HTree α)
    (s s' : α → ℝ)
    (δ : ℝ)
    (hpert : ∀ u v, |(s u - s v) - (s' u - s' v)| ≤ δ)
    (hdom : T.PathDominates s δ) :
    T.eval s' = T.eval s := by
  induction T with
  | leaf a => rfl
  | node L R ihL ihR =>
    simp only [HTree.PathDominates] at hdom
    simp only [HTree.eval]
    split at hdom
    · obtain ⟨hwin, hLdom⟩ := hdom
      rw [ihL hLdom]
      split
      · rfl
      · exfalso
        push_neg at *
        have hmem : R.eval s' ∈ R.classes := HTree.eval_mem_classes R s'
        have h1 : δ < s (L.eval s) - s (R.eval s') := hwin _ hmem
        have h2 : |(s (L.eval s) - s (R.eval s')) - (s' (L.eval s) - s' (R.eval s'))| ≤ δ :=
          hpert _ _
        rcases abs_le.mp h2 with ⟨h3, h4⟩
        linarith
    · obtain ⟨hwin, hRdom⟩ := hdom
      rw [ihR hRdom]
      split
      · exfalso
        push_neg at *
        have hmem : L.eval s' ∈ L.classes := HTree.eval_mem_classes L s'
        have h1 : δ < s (R.eval s) - s (L.eval s') := hwin _ hmem
        have h2 : |(s (R.eval s) - s (L.eval s')) - (s' (R.eval s) - s' (L.eval s'))| ≤ δ :=
          hpert _ _
        rcases abs_le.mp h2 with ⟨h3, h4⟩
        linarith
      · rfl
