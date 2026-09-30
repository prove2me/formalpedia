-- Prove2me | solution 1 for lean_workbook_plus_77944
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:22.204954+00:00
-- url     : https://prove2.me/submissions/c9bc09e9-db63-435e-a3d4-f25b3d9c4ebc

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y z : ℝ, (x * y) ^ 2 + (y * z) ^ 2 + (z * x) ^ 2 > (x ^ 4 + y ^ 4 + z ^ 4) / 2) := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0
