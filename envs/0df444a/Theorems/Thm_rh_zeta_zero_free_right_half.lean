-- Prove2me | Theorems.Thm_rh_zeta_zero_free_right_half
-- name    : rh_zeta_zero_free_right_half
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T15:01:21.666299+00:00
-- url     : https://prove2.me/theorems/ac5dcd0e-e39e-4bf2-a9f1-26993186a3b3
-- statement:
--   The Riemann zeta function has no zeros in the right half of the critical strip, i.e., for $\operatorname{Re}(s) \in (1/2, 1)$.

import Mathlib

import Mathlib

theorem rh_zeta_zero_free_right_half (s : ℂ) (h1 : (1 : ℝ) / 2 < s.re) (h2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  sorry
