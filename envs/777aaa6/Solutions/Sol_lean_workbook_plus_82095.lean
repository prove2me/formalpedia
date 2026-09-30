-- Prove2me | solution 1 for lean_workbook_plus_82095
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:07.754025+00:00
-- url     : https://prove2.me/submissions/2ab17822-6708-4701-916a-ba31a0c23202

import Mathlib

theorem solution : ¬ (∀ (k : ℤ), k > 3 →
    ¬ (∃ x y z : ℤ, x^2 + y^2 + z^2 = k * x * y * z)) := by
  intro h
  apply h 4 (by norm_num)
  exact ⟨0, 0, 0, by norm_num⟩
