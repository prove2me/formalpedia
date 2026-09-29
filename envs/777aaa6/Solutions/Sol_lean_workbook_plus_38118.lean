-- Prove2me | solution 1 for lean_workbook_plus_38118
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:42.439037+00:00
-- url     : https://prove2.me/submissions/dcb3c52f-e363-496f-b55a-9da8a7295746

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y z : ℝ} : 0 ≤ 1 / 2 * (x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 + z ^ 2 * (x - y) ^ 2) := by
  (intros; positivity)
