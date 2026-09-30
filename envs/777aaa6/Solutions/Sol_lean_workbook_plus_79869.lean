-- Prove2me | solution 1 for lean_workbook_plus_79869
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:45.303422+00:00
-- url     : https://prove2.me/submissions/4a40d72f-488e-4abe-ab66-6241cfe7efed

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ,
    (x - y) * (x + y - 2 * z + 5) = 0 ∧
    (y - z) * (y + z - 2 * x + 5) = 0 ∧
    (z - x) * (z + x - 2 * y + 5) = 0) := by
  intro h
  have hbad := h 1 0 0
  norm_num at hbad
