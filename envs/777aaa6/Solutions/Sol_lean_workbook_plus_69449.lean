-- Prove2me | solution 1 for lean_workbook_plus_69449
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:17.733668+00:00
-- url     : https://prove2.me/submissions/f5332704-e1ed-4a54-a3d3-d916304cce53

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ n : ℕ, 27 * n ^ 3 + 9 * n ^ 2 + 9 * n + 1 = (3 * n + 1) ^ 3) := by
  intro h
  have bad := h 1
  norm_num at bad
