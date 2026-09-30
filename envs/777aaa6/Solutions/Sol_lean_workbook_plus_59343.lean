-- Prove2me | solution 1 for lean_workbook_plus_59343
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:53.107062+00:00
-- url     : https://prove2.me/submissions/caca1b53-8170-4ef2-a478-145bd1c88ff8

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf : ∀ x ≠ 0, f x + (1/x) * f (-1/x) = 3) : f 2 = 3/4 := by
  have h1 := hf 2 (by norm_num)
  have h2 := hf (-1/2) (by norm_num)
  have e1 : (-1 : ℝ) / (-1/2) = 2 := by norm_num
  have e2 : (1 : ℝ) / (-1/2) = -2 := by norm_num
  rw [e1, e2] at h2
  linarith
