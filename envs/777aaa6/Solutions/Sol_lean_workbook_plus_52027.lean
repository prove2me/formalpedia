-- Prove2me | solution 1 for lean_workbook_plus_52027
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:06.850103+00:00
-- url     : https://prove2.me/submissions/f6e88e6a-3f8f-41ac-944c-0e80cf2122bc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b * c = 1) :
  (a + 2)^8 ≥ 243 * (2 * a^2 + 1) * (2 * a + 1)^2 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a + 2)^8) - (243 * (2 * a^2 + 1) * (2 * a + 1)^2) := by
    calc
      0 ≤ (13 : ℝ) * (1) * ((1 + ((-1) * a)))^2 + (175 : ℝ) * (1) * ((a + ((-1) * (a ^ 2))))^2 + (146 : ℝ) * (1) * ((a + ((-1) * (a ^ 3))))^2 + (1 : ℝ) * (1) * (((a ^ 2) + ((-1) * (a ^ 4))))^2 + (78 : ℝ) * (a) * ((1 + ((-1) * (a ^ 2))))^2 + (354 : ℝ) * (a) * ((a + ((-1) * (a ^ 2))))^2 + (16 : ℝ) * (a) * (((a ^ 2) + ((-1) * (a ^ 3))))^2 := by positivity
      _ = ((a + 2)^8) - (243 * (2 * a^2 + 1) * (2 * a + 1)^2) := by ring
  exact sub_nonneg.mp h
