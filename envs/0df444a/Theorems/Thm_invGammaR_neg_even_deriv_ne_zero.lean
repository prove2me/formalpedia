-- Prove2me | Theorems.Thm_invGammaR_neg_even_deriv_ne_zero
-- name    : invGammaR_neg_even_deriv_ne_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:32:24.623458+00:00
-- url     : https://prove2.me/theorems/c5d8cba9-f016-494c-847b-a11094ea0935
-- title:
--   The reciprocal real Gamma factor has simple zeros at negative even integers
-- statement:
--   The reciprocal of the real Gamma factor has nonzero derivative at every negative even integer. Thus these zeros are simple.
-- source:
--   Derived from the Gamma functional equation and the simple zeros of the reciprocal complex Gamma function at nonpositive integers.

import Mathlib
import Theorems.Thm_invGamma_neg_nat_deriv_ne_zero

open Complex

theorem invGammaR_neg_even_deriv_ne_zero (n : ℕ) :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) (-2 * ((n + 1 : ℕ) : ℂ)) ≠ 0 := by sorry
