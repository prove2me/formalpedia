-- Prove2me | solution 1 for LabelEntropy.kl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:29:09.960079+00:00
-- url     : https://prove2.me/submissions/a3af1ee2-6a0d-4424-8593-9e41512e89e1

-- Sol generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_LabelEntropy_gibbs_term
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
theorem solution{s : Finset ι} {a b : ι → ℝ}
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hac : ∀ i ∈ s, b i = 0 → a i = 0)
    (hsum : ∑ i ∈ s, b i ≤ ∑ i ∈ s, a i) :
    0 ≤ ∑ i ∈ s, a i * (Real.logb 2 (a i) - Real.logb 2 (b i)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ i ∈ s, (a i - b i) / Real.log 2
      ≤ a i * (Real.logb 2 (a i) - Real.logb 2 (b i)) :=
    fun i hi => gibbs_term (ha i hi) (hb i hi) (hac i hi)
  have h1 : ∑ i ∈ s, (a i - b i) / Real.log 2
      ≤ ∑ i ∈ s, a i * (Real.logb 2 (a i) - Real.logb 2 (b i)) :=
    Finset.sum_le_sum hterm
  have h2 : ∑ i ∈ s, (a i - b i) / Real.log 2
      = ((∑ i ∈ s, a i) - ∑ i ∈ s, b i) / Real.log 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have h3 : 0 ≤ ((∑ i ∈ s, a i) - ∑ i ∈ s, b i) / Real.log 2 :=
    div_nonneg (by linarith) hlog2.le
  linarith [h1, h2 ▸ h3]
