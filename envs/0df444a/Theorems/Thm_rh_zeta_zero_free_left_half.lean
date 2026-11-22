-- Prove2me | Theorems.Thm_rh_zeta_zero_free_left_half
-- name    : rh_zeta_zero_free_left_half
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T15:01:18.30968+00:00
-- url     : https://prove2.me/theorems/598cf64f-e9e1-4747-8dcb-736499dda350
-- statement:
--   The Riemann zeta function has no zeros in the left half of the critical strip, i.e., for $\operatorname{Re}(s) \in (0, 1/2)$.

import Mathlib

import Mathlib

theorem rh_zeta_zero_free_left_half (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < (1 : ℝ) / 2) :
    riemannZeta s ≠ 0 := by
  sorry
