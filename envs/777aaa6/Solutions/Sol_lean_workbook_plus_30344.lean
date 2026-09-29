-- Prove2me | solution 1 for lean_workbook_plus_30344
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:33.201001+00:00
-- url     : https://prove2.me/submissions/c28254a2-333a-4965-b817-c693a177cc99

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, 3 * (a ^ 2 * b + a * b ^ 2) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) ^ 3 := by
  intro a b
  intros
  have h : (0 : ℝ) ≤ (4 * (a ^ 2 + b ^ 2) ^ 3) - (3 * (a ^ 2 * b + a * b ^ 2) ^ 2) := by
    calc
      0 ≤ ((9 / 104) : ℝ) * (((b ^ 3) + (2 * a * (b ^ 2))))^2 + ((9 / 104) : ℝ) * (((b ^ 3) + ((-2) * a * (b ^ 2))))^2 + ((105 / 52) : ℝ) * (((b ^ 3) + (2 * b * (a ^ 2))))^2 + ((14 / 13) : ℝ) * (((b ^ 3) + ((-1) * (a ^ 3))))^2 + ((19 / 26) : ℝ) * (((b ^ 3) + ((-2) * (a ^ 3))))^2 + ((3 / 13) : ℝ) * (((a * (b ^ 2)) + ((-2) * b * (a ^ 2))))^2 := by positivity
      _ = (4 * (a ^ 2 + b ^ 2) ^ 3) - (3 * (a ^ 2 * b + a * b ^ 2) ^ 2) := by ring
  exact sub_nonneg.mp h
