-- Prove2me | solution 1 for lean_workbook_plus_64933
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:08.711289+00:00
-- url     : https://prove2.me/submissions/1d544ba1-ac42-4f6a-90a4-43e38523aeb3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 18)
  (h₂ : a + b = 13 / 5 * c)
  (h₃ : b = 8 / 5 * a)
  (h₄ : x = 45 / 2 - 90 / 13) :
  x = 405 / 26 := by
  (intros; linarith)
