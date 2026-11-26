-- Prove2me | Theorems.Thm_exists_tendsto_polynomial_companions_of_add_one_div_bounds
-- name    : exists_tendsto_polynomial_companions_of_add_one_div_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:39.844105+00:00
-- url     : https://prove2.me/theorems/5a036bce-2604-553f-9538-fe6408aed0bb
-- title:
--   exists tendsto polynomial companions of add one div bounds: exists tendsto polynomial companions of add one div bounds
-- statement:
--   Additive `1 / (j + 1)` errors in polynomial sup norm can be removed by
--   rescaling without changing the operator-norm limit.  The explicit zero-case
--   hypothesis is necessary: a sequence with exact bound zero consists of zero
--   polynomials, so its operator limit must be zero.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L91-L116
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolynomialCompanionNormalization.lean#L91-L116

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_PolynomialCompanionNormalization
set_option autoImplicit false
open Filter
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_tendsto_polynomial_companions_of_add_one_div_bounds
    (A : E →L[ℂ] E) (S : Set ℂ) (m : ℝ) (hm : 0 ≤ m)
    (G : E →L[ℂ] E) (hGzero : m = 0 → G = 0)
    (r : ℕ → Polynomial ℂ)
    (hr : ∀ j, polynomialSupNorm (r j) S ≤
      m + 1 / ((j : ℝ) + 1))
    (hrlim : Tendsto (fun j ↦ Polynomial.aeval A (r j)) atTop (nhds G)) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) S ≤ m) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop (nhds G) := by sorry
