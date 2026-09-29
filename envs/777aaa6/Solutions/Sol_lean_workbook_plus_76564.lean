-- Prove2me | solution 1 for lean_workbook_plus_76564
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:39.467142+00:00
-- url     : https://prove2.me/submissions/f9b3b53a-e65e-4cd5-81de-2f20c402f069

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  (intros; linarith)
