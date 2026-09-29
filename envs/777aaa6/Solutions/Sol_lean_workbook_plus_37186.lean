-- Prove2me | solution 1 for lean_workbook_plus_37186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:18.487905+00:00
-- url     : https://prove2.me/submissions/91b6f7c9-9776-4411-b2d9-d233a65cd219

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^4 * b^4 + b^4 * c^4 + c^4 * a^4 ≥ a^2 * b^2 * c^2 * (a^2 + b^2 + c^2) := by
  intros
  have h : (0 : ℝ) ≤ (a^4 * b^4 + b^4 * c^4 + c^4 * a^4) - (a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((((b ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (c ^ 2))))^2 + ((1 / 2) : ℝ) * ((((b ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * ((((a ^ 2) * (c ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2))))^2 := by positivity
      _ = (a^4 * b^4 + b^4 * c^4 + c^4 * a^4) - (a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)) := by ring
  exact sub_nonneg.mp h
