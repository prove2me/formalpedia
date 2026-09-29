-- Prove2me | solution 1 for lean_workbook_plus_9200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:20.191858+00:00
-- url     : https://prove2.me/submissions/ec7e4968-4e14-41f2-ab32-f281746a99c5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b : ℝ) : (49 * b^6 + 54 * b^5 + 155 * b^4 + 68 * b^3 + 139 * b^2 + 14 * b + 49) * (b - 1)^2 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ ((49 * b^6 + 54 * b^5 + 155 * b^4 + 68 * b^3 + 139 * b^2 + 14 * b + 49) * (b - 1)^2) - (0) := by
    calc
      0 ≤ (42 : ℝ) * ((1 + ((-1) * b)))^2 + (7 : ℝ) * ((1 + ((-1) * (b ^ 3))))^2 + (91 : ℝ) * ((b + ((-1) * (b ^ 2))))^2 + (27 : ℝ) * ((b + ((-1) * (b ^ 4))))^2 + (67 : ℝ) * (((b ^ 2) + ((-1) * (b ^ 3))))^2 + (22 : ℝ) * (((b ^ 3) + ((-1) * (b ^ 4))))^2 := by positivity
      _ = ((49 * b^6 + 54 * b^5 + 155 * b^4 + 68 * b^3 + 139 * b^2 + 14 * b + 49) * (b - 1)^2) - (0) := by ring
  exact sub_nonneg.mp h
