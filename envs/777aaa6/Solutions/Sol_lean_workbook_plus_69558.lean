-- Prove2me | solution 1 for lean_workbook_plus_69558
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:33.51402+00:00
-- url     : https://prove2.me/submissions/5f08e2cd-ba63-47d0-9e45-24ccbb358019

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w x y z : ℝ)
  (h₀ : w + x = 42)
  (h₁ : x + y = 52)
  (h₂ : y + z = 60) :
  (w + z) / 2 = 25 := by
  (intros; linarith)
