-- Prove2me | solution 1 for LabelEntropy.kl_fiber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:30:30.926263+00:00
-- url     : https://prove2.me/submissions/50ba76a6-0513-4bfe-bc0a-2826373528d2

-- Sol generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_LabelEntropy_kl_nonneg
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
theorem solution{s : Finset ι} {v w : ι → ℝ}
    (hv : ∀ x ∈ s, 0 ≤ v x) (hvw : ∀ x ∈ s, v x ≤ w x)
    (hWpos : 0 < ∑ x ∈ s, w x) :
    0 ≤ ∑ x ∈ s, v x *
      ((Real.logb 2 (∑ y ∈ s, w y) - Real.logb 2 (w x))
        - (Real.logb 2 (∑ y ∈ s, v y) - Real.logb 2 (v x))) := by
  set W := ∑ y ∈ s, w y with hW
  set V := ∑ y ∈ s, v y with hV
  have hw : ∀ x ∈ s, 0 ≤ w x := fun x hx => le_trans (hv x hx) (hvw x hx)
  have hVnonneg : 0 ≤ V := Finset.sum_nonneg hv
  -- the comparison measure
  set b : ι → ℝ := fun x => w x * V / W with hbdef
  have hbnonneg : ∀ x ∈ s, 0 ≤ b x := fun x hx =>
    div_nonneg (mul_nonneg (hw x hx) hVnonneg) hWpos.le
  have hbsum : ∑ x ∈ s, b x = V := by
    simp only [hbdef]
    rw [← Finset.sum_div, ← Finset.sum_mul, ← hW]
    field_simp
  have hac : ∀ x ∈ s, b x = 0 → v x = 0 := by
    intro x hx hbx
    simp only [hbdef, div_eq_zero_iff] at hbx
    rcases hbx with h | h
    · rcases mul_eq_zero.mp h with hwx | hVzero
      · exact le_antisymm (by rw [← hwx]; exact hvw x hx) (hv x hx)
      · -- V = 0 with v nonneg forces v x = 0
        have : ∀ y ∈ s, v y = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg hv).mp (hV ▸ hVzero)
        exact this x hx
    · exact absurd h (ne_of_gt hWpos)
  have hkl := kl_nonneg (a := v) (b := b) hv hbnonneg hac (by rw [hbsum])
  refine le_trans hkl (le_of_eq (Finset.sum_congr rfl fun x hx => ?_))
  rcases eq_or_lt_of_le (hv x hx) with h0 | hpos
  · simp [← h0]
  · -- here v x > 0, hence w x > 0 and V > 0
    have hwx : 0 < w x := lt_of_lt_of_le hpos (hvw x hx)
    have hVpos : 0 < V := lt_of_lt_of_le hpos (hV ▸ Finset.single_le_sum hv hx)
    have hbx : b x = w x * V / W := rfl
    have : Real.logb 2 (b x) = Real.logb 2 (w x) + Real.logb 2 V - Real.logb 2 W := by
      rw [hbx, Real.logb_div (by positivity) (ne_of_gt hWpos), Real.logb_mul (ne_of_gt hwx)
        (ne_of_gt hVpos)]
    rw [this]
    ring
