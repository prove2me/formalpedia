-- Prove2me | solution 1 for lean_workbook_plus_82819
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:06.378388+00:00
-- url     : https://prove2.me/submissions/3d180850-8bf5-4675-b5e8-15887c168a1e

import Mathlib

theorem solution : ¬ (∀ a b : ℤ,
    a + b + 1 ∣ (a + b) * (a + b + 1) - (4 * a * b - 1)) := by
  intro h
  have hbad := h 1 2
  norm_num at hbad
