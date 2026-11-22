-- Prove2me | Theorems.Thm_sum_choose_le_exp_pow
-- name    : sum_choose_le_exp_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:01.708954+00:00
-- url     : https://prove2.me/theorems/8c3f4e27-bf19-4acc-8f2a-864a03adeeb2
-- title:
--   sum choose le exp pow: sum choose le exp pow
-- statement:
--   Pure combinatorial inequality: ∑_{i=0}^d C(m,i) ≤ (em/d)^d for d ≤ m, d ≥ 1.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L713-L796
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L713-L796

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), Nat.choose m i : ℝ) ≤ (Real.exp 1 * ↑m / ↑d) ^ d := by sorry
