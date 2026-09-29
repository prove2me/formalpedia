-- Prove2me | solution 1 for lean_workbook_plus_52386
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:41.218514+00:00
-- url     : https://prove2.me/submissions/df0dd590-67c8-48a6-a197-e55050ad8977

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (h₁ : a^2 + b^2 = c^2) (h₂ : 0 < a ∧ 0 < b ∧ 0 < c) (h₃ : a < b) (h₄ : b < c) : a + b > c := by
  (intros; nlinarith)
