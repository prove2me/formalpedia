-- Prove2me | solution 1 for lean_workbook_plus_16375
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:08.328613+00:00
-- url     : https://prove2.me/submissions/2b06783f-dd99-4e06-a75f-d537104df5fa

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (a^2 + x^2) * (b^2 + y^2) * (c^2 + z^2) ≥ (a * b * z + b * c * x + c * a * y - x * y * z)^2 := by
  have key : (a^2 + x^2) * (b^2 + y^2) * (c^2 + z^2)
      = (a * b * c - c * x * y - a * y * z - b * x * z)^2
        + (a * b * z + b * c * x + c * a * y - x * y * z)^2 := by ring
  rw [key]
  nlinarith [sq_nonneg (a * b * c - c * x * y - a * y * z - b * x * z)]
