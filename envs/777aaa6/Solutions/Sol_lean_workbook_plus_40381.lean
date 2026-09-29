-- Prove2me | solution 1 for lean_workbook_plus_40381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:26.934013+00:00
-- url     : https://prove2.me/submissions/02c8c2cb-0650-4cf8-903a-84ec8d1efd4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p i j : ℝ)
  (h₀ : 0 < p)
  (h₁ : 0 < i)
  (h₂ : 0 < j) :
  ((p * (1 + i / 100) * (1 + j / 100) - p) / p) * 100 = i + j + (i * j / 100) := by
  (intros; field_simp; ring)
