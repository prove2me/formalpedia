-- Prove2me | solution 1 for LabelEntropy.D_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:33:51.202745+00:00
-- url     : https://prove2.me/submissions/cb7e7cb6-bf97-47fd-9090-fe081d589be5

-- Sol generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_LabelEntropy_D_eq
/-
# Entropy deficit of a label coarsening

## Context (FACT round-29 #2, "THE-ORIGINAL-STANDS")

The audit of paper 99's rebuild turned on a purely information-theoretic fact:
merging distinct labels can only *destroy* label entropy, never create it, and
the amount destroyed is controlled by a nonnegative **deficit** functional.

This file develops that functional from scratch (Mathlib has no Shannon entropy
for finitely supported weight functions), in bits, with the standard convention
`0 · log 0 = 0` — which is automatic in Lean because `Real.logb 2 0 = 0`.

Main results:

* `D_eq` — closed form of the deficit `D s w = ∑ w x · (log₂ W − log₂ (w x))`;
* `D_nonneg` — the deficit of a nonnegative weight vector is `≥ 0`
  (equivalently: `nlp (∑ w) ≤ H w`, i.e. *merging a block loses entropy*);
* `kl_nonneg` — Gibbs' inequality in unnormalised form, with the zero
  convention and an explicit absolute-continuity hypothesis (which is
  **necessary**: see `kl_neg_without_absolute_continuity`);
* `D_superadditive` — concavity of entropy in deficit form: the total deficit
  of a family of weight vectors is at most the deficit of their sum.  This is
  the engine of the data-processing inequality proved in
  `Applications.JointLabelReconciliation`;
* `D_pos_of_two_positive` — a *strict* loss: whenever a merged block contains
  two strictly positive masses, entropy strictly drops.
-/

open LabelEntropy

open Finset Real

variable {ι κ : Type*}









/-! ## Gibbs' inequality (unnormalised, base 2) -/




/-! ## Concavity of entropy, in deficit form -/



/-! ## Strict loss -/



open LabelEntropy in
theorem solution{s : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ D s w := by
  rw [D_eq]
  refine Finset.sum_nonneg fun i hi => ?_
  rcases eq_or_lt_of_le (hw i hi) with h0 | hpos
  · simp [← h0]
  · have hle : w i ≤ ∑ j ∈ s, w j := Finset.single_le_sum hw hi
    have hS : (0:ℝ) < ∑ j ∈ s, w j := lt_of_lt_of_le hpos hle
    have : Real.logb 2 (w i) ≤ Real.logb 2 (∑ j ∈ s, w j) :=
      Real.logb_le_logb_of_le (by norm_num) hpos hle
    have := sub_nonneg.mpr this
    positivity
