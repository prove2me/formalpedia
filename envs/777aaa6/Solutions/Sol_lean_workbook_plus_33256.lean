-- Prove2me | solution 1 for lean_workbook_plus_33256
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:44.02921+00:00
-- url     : https://prove2.me/submissions/eb417691-1a81-4b85-95a8-eb001ecd545d

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : 4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x * y + y * z + x * z) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
