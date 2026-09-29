-- Prove2me | solution 1 for lean_workbook_plus_71682
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:34.201199+00:00
-- url     : https://prove2.me/submissions/7dc79e0c-3dc3-4cd2-8d4f-e3862a79320d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ a b c : ℝ, (a^2 + b^2 + c^2 - a * b - b * c - c * a)^2 + (a - b * c)^2 + (b - a * c)^2 + (c - a * b)^2 ≥ 0 := by
  (intros; positivity)
