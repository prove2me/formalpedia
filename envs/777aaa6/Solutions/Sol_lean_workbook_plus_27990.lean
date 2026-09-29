-- Prove2me | solution 1 for lean_workbook_plus_27990
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:02.453394+00:00
-- url     : https://prove2.me/submissions/6d600710-11e3-41ef-851b-862516d65e42

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h : a + b + c = 0) :
  (a^2 + b^2 + c^2)^3 ≥ 27 * a^2 * b^2 * c^2 + (a - b)^2 * (b - c)^2 * (c - a)^2 := by
  intros
  have p2m_cond_0 : (a + b + c : ℝ) = (0) := by first | assumption | aesop | linarith
  have p2m_cond_0_gap : (0) - (a + b + c) = 0 := by linarith only [p2m_cond_0]
  have h_identity : ((a^2 + b^2 + c^2)^3) - (27 * a^2 * b^2 * c^2 + (a - b)^2 * (b - c)^2 * (c - a)^2) = ((1033 / 6028) : ℝ) * 1 * (((b * (a ^ 2)) + (2 * c * (a ^ 2))))^2 + ((1491 / 24112) : ℝ) * 1 * (((2 * (a ^ 3)) + (b * (a ^ 2))))^2 + ((1491 / 24112) : ℝ) * 1 * ((((-2) * (a ^ 3)) + (b * (a ^ 2))))^2 + ((5389 / 12056) : ℝ) * 1 * (((b * (a ^ 2)) + (2 * a * (b ^ 2))))^2 + ((7583 / 6028) : ℝ) * 1 * (((b * (a ^ 2)) + ((-1) * b * (c ^ 2))))^2 + ((3621 / 12056) : ℝ) * 1 * (((c * (a ^ 2)) + (2 * a * (c ^ 2))))^2 + ((5723 / 6028) : ℝ) * 1 * (((c * (a ^ 2)) + ((-1) * c * (b ^ 2))))^2 + ((71 / 1096) : ℝ) * 1 * (((c * (a ^ 2)) + ((-2) * c * (b ^ 2))))^2 + ((639 / 6028) : ℝ) * 1 * (((a ^ 3) + (b ^ 3)))^2 + ((2407 / 6028) : ℝ) * 1 * (((a ^ 3) + (c ^ 3)))^2 + ((687 / 6028) : ℝ) * 1 * (((a * (b ^ 2)) + ((-2) * a * (c ^ 2))))^2 + ((591 / 6028) : ℝ) * 1 * (((a * (b ^ 2)) + (2 * c * (b ^ 2))))^2 + ((221 / 3014) : ℝ) * 1 * (((2 * (b ^ 3)) + (a * b * c)))^2 + ((1033 / 3014) : ℝ) * 1 * (((a * (c ^ 2)) + (b * (c ^ 2))))^2 + ((2407 / 6028) : ℝ) * 1 * (((b * (c ^ 2)) + (c * (b ^ 2))))^2 + ((3621 / 6028) : ℝ) * 1 * (((b ^ 3) + (c ^ 3)))^2 := by
    linear_combination ((((-1981 / 1507) * a * b * (c ^ 3)) + ((-1981 / 1507) * a * c * (b ^ 3)) + ((-1981 / 1507) * b * c * (a ^ 3)) + ((4995 / 1507) * a * (b ^ 2) * (c ^ 2)) + ((4995 / 1507) * b * (a ^ 2) * (c ^ 2)) + ((4995 / 1507) * c * (a ^ 2) * (b ^ 2)))) * p2m_cond_0_gap
  have h_nonnegative : (0 : ℝ) ≤ ((a^2 + b^2 + c^2)^3) - (27 * a^2 * b^2 * c^2 + (a - b)^2 * (b - c)^2 * (c - a)^2) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
