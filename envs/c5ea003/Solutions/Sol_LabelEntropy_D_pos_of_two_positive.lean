-- Prove2me | solution 1 for LabelEntropy.D_pos_of_two_positive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:33:52.195401+00:00
-- url     : https://prove2.me/submissions/b7bce033-7ee7-43f5-a20f-8280f027919f

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
theorem solution{s : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hwi : 0 < w i) (hwj : 0 < w j) : 0 < D s w := by
  classical
  rw [D_eq]
  set S := ∑ k ∈ s, w k with hS
  have hSi : w i + w j ≤ S := by
    have : w i + w j = ∑ k ∈ ({i, j} : Finset ι), w k := by
      rw [Finset.sum_pair hij]
    rw [this, hS]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k hk _ => hw k hk)
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have hSpos : 0 < S := by linarith
  have hstrict : Real.logb 2 (w i) < Real.logb 2 S :=
    Real.logb_lt_logb (by norm_num) hwi (by linarith)
  have hpos_i : 0 < w i * (Real.logb 2 S - Real.logb 2 (w i)) := by
    have := sub_pos.mpr hstrict
    positivity
  have hrest : ∀ k ∈ s, 0 ≤ w k * (Real.logb 2 S - Real.logb 2 (w k)) := by
    intro k hk
    rcases eq_or_lt_of_le (hw k hk) with h0 | hpos
    · simp [← h0]
    · have hle : w k ≤ S := hS ▸ Finset.single_le_sum hw hk
      have : Real.logb 2 (w k) ≤ Real.logb 2 S := Real.logb_le_logb_of_le (by norm_num) hpos hle
      have := sub_nonneg.mpr this
      positivity
  exact Finset.sum_pos' hrest ⟨i, hi, hpos_i⟩
