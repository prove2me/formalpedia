-- Prove2me | solution 1 for lean_workbook_plus_40957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:31.325423+00:00
-- url     : https://prove2.me/submissions/7cffefbb-8990-4461-a516-f6fe03cbb773

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^8 + b^8 + c^8 ≥ a^4 * b^4 + b^4 * c^4 + c^4 * a^4 := by
  intros
  have h : (0 : ℝ) ≤ (a^8 + b^8 + c^8) - (a^4 * b^4 + b^4 * c^4 + c^4 * a^4) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c ^ 4) + ((-1) * (b ^ 4))))^2 + ((1 / 2) : ℝ) * (((c ^ 4) + ((-1) * (a ^ 4))))^2 + ((1 / 2) : ℝ) * (((b ^ 4) + ((-1) * (a ^ 4))))^2 := by positivity
      _ = (a^8 + b^8 + c^8) - (a^4 * b^4 + b^4 * c^4 + c^4 * a^4) := by ring
  exact sub_nonneg.mp h
