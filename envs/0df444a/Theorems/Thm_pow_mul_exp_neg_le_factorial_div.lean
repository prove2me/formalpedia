-- Prove2me | Theorems.Thm_pow_mul_exp_neg_le_factorial_div
-- name    : pow_mul_exp_neg_le_factorial_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:22.919005+00:00
-- url     : https://prove2.me/theorems/2821f256-7b1f-4f7c-9602-b2705d570460
-- title:
--   pow mul exp neg le factorial div: pow mul exp neg le factorial div
-- statement:
--   Key arithmetic lemma for PAC bound: for t > 0, t^d * exp(-t) ≤ (d+1)!/t.
--       Follows from exp(t) ≥ t^(d+1)/(d+1)! (partial sum of Taylor series).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L566-L581
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L566-L581

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem pow_mul_exp_neg_le_factorial_div {d : ℕ} {t : ℝ} (ht : 0 < t) :
    t ^ d * Real.exp (-t) ≤ ↑((d + 1).factorial) / t := by sorry
