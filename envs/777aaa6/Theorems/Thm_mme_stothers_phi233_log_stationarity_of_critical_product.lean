-- Prove2me | Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
-- name    : mme_stothers_phi233_log_stationarity_of_critical_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:40:37.18355+00:00
-- url     : https://prove2.me/theorems/0af3408e-5081-473a-835d-49f92eaf1110
-- title:
--   Logarithmic phi_233 stationarity from the critical product equation
-- statement:
--   Let $a,b,c,d$ be positive real profile weights satisfying the multiplicative critical-point equation
--
--   $$
--   a^2d=b^2c.
--   $$
--
--   Then the derivative of the symmetric ten-label entropy vanishes along the one-dimensional fixed-marginal fibre:
--
--   $$
--   2[-\log(a/2)-1]-2[-\log(b/2)-1]-[-\log(c/2)-1]+[-\log(d/2)-1]=0.
--   $$
--
--   This converts the algebraic stationarity certificate used for the $\varphi_{233}$ profile into the additive logarithmic certificate required by its entropy tangent bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v) and the entropy optimization surrounding Equation (3.6), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_stothers_phi233_log_stationarity_of_critical_product
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (hcritical : a ^ (2 : ℕ) * d = b ^ (2 : ℕ) * c) :
    2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0 := by
  sorry
