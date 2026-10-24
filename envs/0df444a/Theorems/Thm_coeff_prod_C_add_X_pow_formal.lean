-- Prove2me | Theorems.Thm_coeff_prod_C_add_X_pow_formal
-- name    : coeff_prod_C_add_X_pow_formal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:07:54.350124+00:00
-- url     : https://prove2.me/theorems/8272a078-c278-4bf1-b748-651cdcb575d4
-- title:
--   Coefficient of a product of shifted variable powers
-- statement:
--   The coefficient indexed by `A` in the product of shifted variable powers is the product of the binomial coefficients times the scalar series raised to the sum of the remaining exponents. If a requested degree exceeds an exponent, the corresponding binomial coefficient makes the result zero.

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Complex.Basic
open scoped BigOperators

theorem coeff_prod_C_add_X_pow_formal
    {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) (c : PowerSeries ℂ) :
    MvPolynomial.coeff A
      (∏ i : Fin m, (MvPolynomial.C c + MvPolynomial.X i) ^ a i :
        MvPolynomial (Fin m) (PowerSeries ℂ)) =
      PowerSeries.C ((∏ i, (a i).choose (A i) : ℕ) : ℂ) *
        c ^ (∑ i : Fin m, (a i - A i)) := by sorry
