-- Prove2me | Theorems.Thm_gpy_twistedExp_eq_pow
-- name    : gpy_twistedExp_eq_pow
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T05:07:32.576866+00:00
-- url     : https://prove2.me/theorems/6f375f66-2292-4896-9e01-2fc9fb06b9a8
-- title:
--   Exact polynomial form of the unconditional twisted exponential factor
-- statement:
--   The exponential factor exp (2 (k+1)^2 (log Q + 2)) in the unconditional twisted absolute bound equals exp (4 (k+1)^2) * Q^(2 (k+1)^2): it is polynomial in Q, not polylogarithmic. This is an unconditional identity, and it is precisely why the unconditional bound cannot by itself show any sum is o(1) relative to a polylog-scale main term. No defect smallness is claimed.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_twistedExp_eq_pow {k : ℕ} {Q : ℕ} (hQ : 0 < Q) :
    Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Q : ℝ) + 2))
      = Real.exp (4 * ((k : ℝ) + 1) ^ 2) * (Q : ℝ) ^ (2 * (k + 1) ^ 2) := by sorry
