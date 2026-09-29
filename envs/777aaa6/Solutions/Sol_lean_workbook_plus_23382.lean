-- Prove2me | solution 1 for lean_workbook_plus_23382
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:17.827561+00:00
-- url     : https://prove2.me/submissions/ed64c8b7-d622-42ce-a65f-87d36320a5b8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 ≤ x) : 60 * x^8 + 135 * x^7 + 369 * x^6 + 169 * x^5 + 402 * x^4 + 53 * x^3 - 19 * x^2 + 11 * x + 4 ≥ 0 := by
  intros
  have hpos_x : (0 : ℝ) ≤ x := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (60 * x^8 + 135 * x^7 + 369 * x^6 + 169 * x^5 + 402 * x^4 + 53 * x^3 - 19 * x^2 + 11 * x + 4) - (0) := by
    calc
      0 ≤ (4 : ℝ) * (1) * ((1 + ((-2) * (x ^ 2))))^2 + ((22879 / 2320) : ℝ) * (1) * ((x + ((-2) * (x ^ 2))))^2 + ((72241 / 2320) : ℝ) * (1) * ((x + (2 * (x ^ 3))))^2 + ((287 / 20) : ℝ) * (1) * (((x ^ 2) + ((-2) * (x ^ 3))))^2 + ((8041 / 580) : ℝ) * (1) * (((x ^ 2) + (2 * (x ^ 4))))^2 + ((659 / 580) : ℝ) * (1) * (((x ^ 3) + (2 * (x ^ 4))))^2 + (11 : ℝ) * (x) * ((1 + ((-2) * x)))^2 + ((28099 / 580) : ℝ) * (x) * ((x + (2 * (x ^ 2))))^2 + ((4729 / 145) : ℝ) * (x) * (((x ^ 2) + (2 * (x ^ 3))))^2 := by positivity
      _ = (60 * x^8 + 135 * x^7 + 369 * x^6 + 169 * x^5 + 402 * x^4 + 53 * x^3 - 19 * x^2 + 11 * x + 4) - (0) := by ring
  exact sub_nonneg.mp h
