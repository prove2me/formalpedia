-- Prove2me | solution 1 for lean_workbook_plus_60869
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:37:59.766752+00:00
-- url     : https://prove2.me/submissions/3d43e8bb-7538-416c-9884-8d509c8f9308

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ)
  (h₀ : x = 1)
  (h₁ : y = 1)
  (h₂ : z = 1) :
  |1 + y| + |1 + z| + |x + y| + |y + z| + |z + x| ≤ 12 := by
  subst h₀ h₁ h₂
  norm_num
