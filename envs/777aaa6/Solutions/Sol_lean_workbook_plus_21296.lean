-- Prove2me | solution 1 for lean_workbook_plus_21296
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:26.192967+00:00
-- url     : https://prove2.me/submissions/edca1233-7cba-45f3-9146-b40b51719584

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℝ)
  (h₀ : n ≠ 0)
  (h₁ : n + 3 ≠ 0) :
  1 + 2 / (n^2 + 3 * n) = (n + 1) * (n + 2) / (n * (n + 3)) := by
  (intros; field_simp; ring)
