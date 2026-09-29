-- Prove2me | Theorems.Thm_binomial_prefix_tail_of_linear_gap
-- name    : binomial_prefix_tail_of_linear_gap
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T05:46:13.695297+00:00
-- url     : https://prove2.me/theorems/dd3f5225-dcf8-41b9-a48e-f118f3a86145
-- title:
--   Binomial prefix tail bound with a strict rate in (0,1)
-- statement:
--   For every real c > 0, natural q,t with q > 0, and linear-gap hypothesis (2+c)t ≤ q, the finite prefix sum ∑_{k<t} binom(q-1,k), normalized by 2^q, is at most the q-th power of the explicit rate ((2+c)/(2(1+c))) * (1+c)^(1/(2+c)). The same conjunction records that this rate is strictly between 0 and 1.

import Mathlib
set_option autoImplicit false
open Real
open scoped BigOperators
noncomputable section

theorem binomial_prefix_tail_of_linear_gap (c : ℝ) (hc : 0 < c) (q t : ℕ) (hq : 0 < q) (hqt : (2 + c) * (t : ℝ) ≤ (q : ℝ)) :
    0 < ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) ∧
      ((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c)) < 1 ∧
      (∑ k : Fin t, (Nat.choose (q - 1) k : ℝ)) / (2 : ℝ) ^ q ≤
        (((2 + c) / (2 * (1 + c))) * Real.rpow (1 + c) (1 / (2 + c))) ^ q := by sorry
