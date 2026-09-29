-- Prove2me | solution 1 for lean_workbook_plus_41798
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:56.471829+00:00
-- url     : https://prove2.me/submissions/0bf259a6-5900-475a-915a-111a29cce37e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (n : ℕ) : x = (4:ℝ) / 39 * (10 ^ n - 4) ↔ x = (4:ℝ) / 39 * (10 ^ n - 4) := by
  norm_num
