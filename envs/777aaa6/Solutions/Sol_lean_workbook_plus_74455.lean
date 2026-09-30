-- Prove2me | solution 1 for lean_workbook_plus_74455
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T09:35:57.493628+00:00
-- url     : https://prove2.me/submissions/6deea80e-11cf-4d9d-8f75-ad0e010893a4

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ a b c d : ℝ,
    4 / (a / (1 - a) + b / (1 - b) + c / (1 - c) + d / (1 - d)) ≥ 1) := by
  intro h
  have bad := h (3 / 4) (3 / 4) (3 / 4) (3 / 4)
  norm_num at bad
  have hb : (1 : ℝ) * (3 + 3 + 3 + 3) ≤ 4 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 3 + 3 + 3 + 3)).mp bad
  linarith
