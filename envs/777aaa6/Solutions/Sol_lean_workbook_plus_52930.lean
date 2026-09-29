-- Prove2me | solution 1 for lean_workbook_plus_52930
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:46.195198+00:00
-- url     : https://prove2.me/submissions/e7f1ee79-842c-4bba-812d-818ada47068b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (j s : ℝ)
  (h₀ : 0 < j ∧ 0 < s)
  (h₁ : j + s = 1)
  (h₂ : (3 / 5) * j = (2 / 3) * (6 / 7) * s) :
  (3 / 5) * j + (6 / 7) * s = 30 / 41 := by
  (intros; linarith)
