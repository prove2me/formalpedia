-- Prove2me | solution 1 for lean_workbook_plus_38306
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:35.645693+00:00
-- url     : https://prove2.me/submissions/5b5db40e-369b-4df3-a664-5bfd40a498f8

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) + a^2 * b^2 * c^2 ≥ 1 / 3 := by
  have h1 : a^2 * b^2 * c^2 = 1 := by
    have : a^2 * b^2 * c^2 = (a*b*c)^2 := by ring
    rw [this, habc]; norm_num
  have h2 : 0 < (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) := by positivity
  linarith
