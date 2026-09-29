-- Prove2me | solution 1 for lean_workbook_plus_47746
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:07.129052+00:00
-- url     : https://prove2.me/submissions/89a29006-48db-406b-adb4-0e74ec74a2b8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (b + 2 * a) ^ 2 + (c + 2 * a) ^ 2 ≥ 0 := by
  (intros; positivity)
