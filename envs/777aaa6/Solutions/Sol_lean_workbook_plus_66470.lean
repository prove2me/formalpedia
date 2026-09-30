-- Prove2me | solution 1 for lean_workbook_plus_66470
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:55.936806+00:00
-- url     : https://prove2.me/submissions/09ae89f2-468d-4b26-ac93-cfe591f2974d

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y z : ℝ, (y^2 * x * z / (y + x)^2 * (x * y + z^2) + z^2 * x * y / (y + z)^2 * (z * y + x^2) + x^2 * y * z / (z + x)^2 * (x * z + y^2) ≤ 3 / 8)) := by
  intro h
  have := h 1 1 1
  norm_num at this
