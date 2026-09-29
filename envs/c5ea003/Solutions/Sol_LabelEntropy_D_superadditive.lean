-- Prove2me | solution 1 for LabelEntropy.D_superadditive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:31:40.285264+00:00
-- url     : https://prove2.me/submissions/e23326b8-3645-467b-b539-db91a8df4159

-- Sol generated from Applications/LabelEntropyDeficit.lean
import Mathlib
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_LabelEntropy_D_eq
import Theorems.Thm_LabelEntropy_kl_fiber_nonneg
import Theorems.Thm_LabelEntropy_nlp_zero
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
theorem solution{s : Finset ι} {t : Finset κ} {v : κ → ι → ℝ}
    (hv : ∀ y ∈ t, ∀ x ∈ s, 0 ≤ v y x) :
    ∑ y ∈ t, D s (v y) ≤ D s (fun x => ∑ y ∈ t, v y x) := by
  set w : ι → ℝ := fun x => ∑ y ∈ t, v y x with hwdef
  have hw : ∀ x ∈ s, 0 ≤ w x := fun x hx => Finset.sum_nonneg fun y hy => hv y hy x hx
  have hvw : ∀ y ∈ t, ∀ x ∈ s, v y x ≤ w x := fun y hy x hx =>
    Finset.single_le_sum (f := fun y => v y x) (fun z hz => hv z hz x hx) hy
  rcases eq_or_lt_of_le (Finset.sum_nonneg hw) with hW0 | hWpos
  · -- degenerate: total mass zero, everything vanishes
    have hallw : ∀ x ∈ s, w x = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW0.symm
    have hallv : ∀ y ∈ t, ∀ x ∈ s, v y x = 0 := by
      intro y hy x hx
      exact le_antisymm (by rw [← hallw x hx]; exact hvw y hy x hx) (hv y hy x hx)
    have hL : ∀ y ∈ t, D s (v y) = 0 := by
      intro y hy
      have h1 : ∀ x ∈ s, v y x = 0 := fun x hx => hallv y hy x hx
      have h2 : H s (v y) = 0 :=
        Finset.sum_eq_zero fun x hx => by rw [h1 x hx, nlp_zero]
      have h3 : ∑ x ∈ s, v y x = 0 := Finset.sum_eq_zero h1
      simp [D, h2, h3]
    have hR : D s w = 0 := by
      have h2 : H s w = 0 :=
        Finset.sum_eq_zero fun x hx => by rw [hallw x hx, nlp_zero]
      have h3 : ∑ x ∈ s, w x = 0 := Finset.sum_eq_zero hallw
      simp [D, h2, h3]
    rw [Finset.sum_congr rfl hL, hR]
    simp
  · rw [D_eq]
    have hLHS : ∑ y ∈ t, D s (v y)
        = ∑ y ∈ t, ∑ x ∈ s, v y x *
            (Real.logb 2 (∑ z ∈ s, v y z) - Real.logb 2 (v y x)) :=
      Finset.sum_congr rfl fun y _ => D_eq s (v y)
    have hRHS : ∑ x ∈ s, w x * (Real.logb 2 (∑ z ∈ s, w z) - Real.logb 2 (w x))
        = ∑ y ∈ t, ∑ x ∈ s, v y x *
            (Real.logb 2 (∑ z ∈ s, w z) - Real.logb 2 (w x)) := by
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [hwdef, Finset.sum_mul]
    rw [hLHS, hRHS, ← sub_nonneg, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun y hy => ?_
    have := kl_fiber_nonneg (s := s) (v := v y) (w := w)
      (fun x hx => hv y hy x hx) (fun x hx => hvw y hy x hx) hWpos
    calc (0:ℝ) ≤ ∑ x ∈ s, v y x *
          ((Real.logb 2 (∑ z ∈ s, w z) - Real.logb 2 (w x))
            - (Real.logb 2 (∑ z ∈ s, v y z) - Real.logb 2 (v y x))) := this
      _ = (∑ x ∈ s, v y x * (Real.logb 2 (∑ z ∈ s, w z) - Real.logb 2 (w x)))
            - ∑ x ∈ s, v y x * (Real.logb 2 (∑ z ∈ s, v y z) - Real.logb 2 (v y x)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
