-- Prove2me | solution 1 for lean_workbook_plus_24814
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:45.217454+00:00
-- url     : https://prove2.me/submissions/9aea3d10-cf63-42fd-bd0a-25c2155dabc8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, (a + 2 * c) ^ 2 + (b + 2 * c) ^ 2 ≥ 0 := by
  (intros; positivity)
