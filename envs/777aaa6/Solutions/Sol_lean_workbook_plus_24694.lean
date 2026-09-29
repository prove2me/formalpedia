-- Prove2me | solution 1 for lean_workbook_plus_24694
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:42:28.27486+00:00
-- url     : https://prove2.me/submissions/e613f41a-551d-4770-b6c8-366333a2f0fd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h₁ : |2 * b - 1| ≤ 1) (h₂ : a * (1 - |2 * b - 1|) = 2 * b - 1) : 2 * b * (1 + |a|) = 1 + a + |a| := by
  have hd : 0 ≤ 1-|2*b-1| := by linarith
  rcases le_total 0 a with ha | ha
  · have hp := mul_nonneg ha hd
    rw [h₂] at hp
    rw [abs_of_nonneg ha]
    rw [abs_of_nonneg hp] at h₂
    nlinarith
  · have hp := mul_nonpos_of_nonpos_of_nonneg ha hd
    rw [h₂] at hp
    rw [abs_of_nonpos ha]
    rw [abs_of_nonpos hp] at h₂
    nlinarith
