-- Prove2me | solution 1 for lean_workbook_plus_63559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:52.407185+00:00
-- url     : https://prove2.me/submissions/1fde0016-1a9e-4bcd-97b3-a74c3f384e89

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : (1 + x^2) * (1 + y^2) * (1 + z^2) ≥ (x * y + y * z + x * z - 1)^2 := by
  nlinarith [sq_nonneg (x + y + z - x * y * z)]
