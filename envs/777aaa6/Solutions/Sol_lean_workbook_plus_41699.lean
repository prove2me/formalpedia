-- Prove2me | solution 1 for lean_workbook_plus_41699
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:10.61439+00:00
-- url     : https://prove2.me/submissions/44001333-e77c-466b-8edf-14530c23916a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) (h₁ : a ≥ 1) (h₂ : b + c ≤ -1) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3 := by
  intros
  have p2m_cond_1 : (b + c : ℝ) ≤ (-1) := by first | assumption | aesop | linarith
  have p2m_cond_1_gap : (0 : ℝ) ≤ (-1) - (b + c) := by linarith only [p2m_cond_1]
  have h_identity : (a^4 + b^4 + c^4) - (a^3 + b^3 + c^3) = ((49 / 461) : ℝ) * 1 * ((1 + ((-2) * (b ^ 2))))^2 + ((1 / 6) : ℝ) * 1 * ((a + ((-1) * (a ^ 2))))^2 + ((1 / 6) : ℝ) * 1 * ((a + ((-2) * (a ^ 2))))^2 + ((1 / 12) : ℝ) * 1 * (((a ^ 2) + (2 * b)))^2 + ((1 / 12) : ℝ) * 1 * (((a ^ 2) + (2 * c)))^2 + ((237 / 1844) : ℝ) * 1 * ((b + ((-2) * (b ^ 2))))^2 + ((28 / 461) : ℝ) * 1 * ((b + (2 * b * c)))^2 + ((105 / 922) : ℝ) * 1 * ((b + ((-2) * c)))^2 + ((931 / 5532) : ℝ) * 1 * ((b + (2 * (c ^ 2))))^2 + ((28 / 461) : ℝ) * 1 * (((b ^ 2) + ((-2) * (c ^ 2))))^2 + ((29 / 1383) : ℝ) * 1 * ((c + ((-2) * (c ^ 2))))^2 + ((913 / 55320) : ℝ) * ((-1) - (b + c)) * ((1 + (2 * a)))^2 + ((913 / 55320) : ℝ) * ((-1) - (b + c)) * ((1 + ((-2) * a)))^2 + ((49 / 1844) : ℝ) * ((-1) - (b + c)) * ((1 + ((-2) * b)))^2 + ((557 / 55320) : ℝ) * ((-1) - (b + c)) * ((1 + (2 * c)))^2 + ((2027 / 55320) : ℝ) * ((-1) - (b + c)) * ((1 + ((-2) * c)))^2 + ((147 / 3688) : ℝ) * ((-1) - (b + c)) * ((a + (2 * b)))^2 + ((147 / 3688) : ℝ) * ((-1) - (b + c)) * ((a + ((-2) * b)))^2 + ((1121 / 18440) : ℝ) * ((-1) - (b + c)) * ((a + (2 * c)))^2 + ((1121 / 18440) : ℝ) * ((-1) - (b + c)) * ((a + ((-2) * c)))^2 + ((28 / 461) : ℝ) * ((-1) - (b + c)) * ((b + ((-2) * c)))^2 := by
    ring
  have h_nonnegative : (0 : ℝ) ≤ (a^4 + b^4 + c^4) - (a^3 + b^3 + c^3) := by
    rw [h_identity]
    positivity
  exact sub_nonneg.mp h_nonnegative
