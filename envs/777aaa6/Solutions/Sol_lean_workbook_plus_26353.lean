-- Prove2me | solution 1 for lean_workbook_plus_26353
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:03:35.041843+00:00
-- url     : https://prove2.me/submissions/690e93a2-b6b0-4a4b-bacd-596a9bb0e57c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0)
    (h : x + y + z = 1) : (x + 1) * (y + 2) * (z + 3) ≥ 8 := by
  nlinarith only [h, hx, hy, mul_nonneg hx hy, mul_nonneg hx hz,
    mul_nonneg hy hz, mul_nonneg (mul_nonneg hx hy) hz]
