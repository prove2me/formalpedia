-- Prove2me | solution 1 for HTree.allMarginsAbove_implies_pathDominates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:08:35.785681+00:00
-- url     : https://prove2.me/submissions/4de835ea-3783-47b6-a5c3-98c3b3e24fe9

-- Sol generated from Bridges/HTreeRobust.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
import Definitions.Def_Bridges_HTreeRobust
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



private theorem htree_eval_score_ge {α : Type} [DecidableEq α] (T : HTree α) (s : α → ℝ) :
    ∀ c ∈ T.classes, s c ≤ s (T.eval s) := by
  induction T with
  | leaf a =>
    intro c hc
    simp only [HTree.classes, Finset.mem_singleton] at hc
    subst hc
    simp [HTree.eval]
  | node L R ihL ihR =>
    intro c hc
    simp only [HTree.classes, Finset.mem_union] at hc
    simp only [HTree.eval]
    split
    · rename_i hif
      rcases hc with hc | hc
      · exact ihL c hc
      · exact (ihR c hc).trans hif
    · rename_i hif
      rcases hc with hc | hc
      · exact (ihL c hc).trans (le_of_lt (lt_of_not_ge hif))
      · exact ihR c hc

open HTree in
theorem solution[DecidableEq α]
    (T : HTree α) (s : α → ℝ) (δ : ℝ)
    (h : T.AllMarginsAbove s δ) :
    T.PathDominates s δ := by
  induction T with
  | leaf a => trivial
  | node L R ihL ihR =>
    obtain ⟨habs, ihL', ihR'⟩ := h
    simp only [HTree.PathDominates]
    split
    · rename_i hcmp
      refine ⟨fun c hc => ?_, ihL ihL'⟩
      have h1 : δ < s (L.eval s) - s (R.eval s) := by
        have h2 : |s (L.eval s) - s (R.eval s)| = s (L.eval s) - s (R.eval s) :=
          abs_of_nonneg (by linarith)
        linarith
      linarith [htree_eval_score_ge R s c hc]
    · rename_i hcmp
      refine ⟨fun c hc => ?_, ihR ihR'⟩
      have h1 : δ < s (R.eval s) - s (L.eval s) := by
        have hyx : 0 < s (R.eval s) - s (L.eval s) := by
          have hx : s (R.eval s) > s (L.eval s) := lt_of_not_ge hcmp
          linarith
        rw [abs_sub_comm, abs_of_pos hyx] at habs
        linarith
      linarith [htree_eval_score_ge L s c hc]
