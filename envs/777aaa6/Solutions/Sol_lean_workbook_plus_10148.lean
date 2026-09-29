-- Prove2me | solution 1 for lean_workbook_plus_10148
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:01.298117+00:00
-- url     : https://prove2.me/submissions/87e3b4fe-00f8-4f65-9394-01990074793d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^8 + b^8) ≥ (a^3 + b^3) * (a^5 + b^5) := by
  intros
  
  have h : (0 : ℝ) ≤ (2 * (a^8 + b^8)) - ((a^3 + b^3) * (a^5 + b^5)) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * (1) * ((((-1) * (a ^ 4)) + ((a ^ 2) * (b ^ 2))))^2 + ((1 / 4) : ℝ) * (1) * ((((-1) * (b ^ 4)) + ((a ^ 2) * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (1) * ((((-1) * (b ^ 4)) + (b * (a ^ 3))))^2 + ((1 / 2) : ℝ) * (1) * (((a ^ 4) + ((-1) * a * (b ^ 3))))^2 + ((1 / 4) : ℝ) * (1) * (((a ^ 4) + ((-1) * (b ^ 4))))^2 := by positivity
      _ = (2 * (a^8 + b^8)) - ((a^3 + b^3) * (a^5 + b^5)) := by ring
  exact sub_nonneg.mp h
