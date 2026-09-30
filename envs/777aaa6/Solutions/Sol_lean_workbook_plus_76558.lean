-- Prove2me | solution 1 for lean_workbook_plus_76558
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:09:52.684433+00:00
-- url     : https://prove2.me/submissions/be5ae424-45f0-47b3-8611-0083f29d608b

import Mathlib

set_option autoImplicit false

theorem solution (k : ℕ) (h₀ : 2 ≤ k) :
    (1 : ℝ) / k ^ 2 ≤ 1 / (k * (k - 1)) := by
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast h₀
  apply one_div_le_one_div_of_le
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith
