-- Prove2me | solution 1 for lean_workbook_plus_81865
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:16:50.868641+00:00
-- url     : https://prove2.me/submissions/bd11a81b-e571-402e-82e2-84e5b9bf3e33

import Mathlib

theorem solution : ¬ (∀ x y z : ℝ,
    4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥
      x + y + z + 2 * (x * y + y * z + z * x) + 3) := by
  intro h
  have hbad := h 0 0 0
  norm_num at hbad
