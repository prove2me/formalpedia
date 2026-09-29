-- Prove2me | Theorems.Thm_mme_dwz_multinomial_entropy_upper
-- name    : mme_dwz_multinomial_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:50:29.021855+00:00
-- url     : https://prove2.me/theorems/be0d1abf-ea86-49f6-80e0-c599cd9948d1
-- title:
--   Every integral multinomial type is bounded by its exact Shannon rate
-- statement:
--   Let `w` be a finite nonzero vector of nonnegative integer weights, put $W=\sum_i w_i$, and let $m>0$. For the rational distribution $p_i=w_i/W$, the exact multinomial coefficient satisfies
--
--   $$
--   \binom{Wm}{(w_i m)_{i\in R}}
--   \le \exp\bigl(mW\log(2)H_2(p)\bigr).
--   $$
--
--   Zero-weight symbols are allowed. Unlike a Stirling estimate, this upper bound has no polynomial loss: the left-hand side multiplied by $\prod_i p_i^{w_i m}$ is one nonnegative term of the multinomial expansion of $(\sum_i p_i)^{Wm}=1$, while the reciprocal product is exactly the displayed Shannon exponential. Together with `mme_dwz_multinomial_entropy_polynomial_lower`, this sandwiches every rational type count at its entropy rate and supplies the numerator/denominator estimates used in DWZ Equation (23).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Lemma 6.7 and Equation (23), printed pp. 54-56 (PDF pp. 55-57); standard method-of-types upper bound from the multinomial theorem.

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_multinomial_entropy_upper
    {R : Type*} [Fintype R] (w : R → ℕ)
    (m : ℕ) (hm : 0 < m) (hW : 0 < ∑ i, w i) :
    (Nat.multinomial Finset.univ (fun i ↦ w i * m) : ℝ) ≤
      Real.exp
        ((m : ℝ) * (((∑ i, w i : ℕ) : ℝ) * Real.log 2 *
          mme_modern_entropyBits
            (fun i ↦ (w i : ℝ) / ((∑ j, w j : ℕ) : ℝ)))) := by sorry
