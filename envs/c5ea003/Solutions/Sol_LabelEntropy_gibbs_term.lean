-- Prove2me | solution 1 for LabelEntropy.gibbs_term
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:27:19.193278+00:00
-- url     : https://prove2.me/submissions/2e52ed25-eacc-4d62-a193-4236d1b9709b

-- Sol generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
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
theorem solution{a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : b = 0 → a = 0) :
    (a - b) / Real.log 2 ≤ a * (Real.logb 2 a - Real.logb 2 b) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases eq_or_lt_of_le ha with h0 | hapos
  · have hb' : 0 ≤ b := hb
    simp only [← h0, zero_mul, zero_sub]
    have : (0 - b) / Real.log 2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) hlog2.le
    simpa using this
  · have hbpos : 0 < b := by
      rcases eq_or_lt_of_le hb with hb0 | hbp
      · exact absurd (hac hb0.symm) (by linarith)
      · exact hbp
    have hlog : Real.log (b / a) ≤ b / a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hbpos hapos)
    have hsplit : Real.log (b / a) = Real.log b - Real.log a :=
      Real.log_div (ne_of_gt hbpos) (ne_of_gt hapos)
    have key : Real.log a - Real.log b ≥ 1 - b / a := by
      rw [hsplit] at hlog; linarith
    have hmul : a * (Real.log a - Real.log b) ≥ a * (1 - b / a) := by
      exact mul_le_mul_of_nonneg_left key hapos.le
    have hcancel : a * (1 - b / a) = a - b := by
      field_simp
    have hkey : a - b ≤ a * (Real.log a - Real.log b) := by
      rw [← hcancel]; exact hmul
    have hrw : a * (Real.logb 2 a - Real.logb 2 b)
        = (a * (Real.log a - Real.log b)) / Real.log 2 := by
      simp only [Real.logb]
      ring
    rw [hrw]
    gcongr
