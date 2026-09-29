-- Prove2me | solution 1 for lean_workbook_plus_82245
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:44.043689+00:00
-- url     : https://prove2.me/submissions/88e64cb3-df82-4750-ad8e-ac6166746561

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 / Real.sqrt (b^2 + c^2) + b^2 / Real.sqrt (c^2 + a^2) + c^2 / Real.sqrt (a^2 + b^2)) ≥ 0 := by
  (intros; positivity)
