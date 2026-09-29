-- Prove2me | solution 1 for lean_workbook_plus_10229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:13.062998+00:00
-- url     : https://prove2.me/submissions/982edfd2-ed5a-433f-9c71-9153a92b3118

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 2 * (a * b + a * c + b * c + b * d + c * d + c * e + d * e + d * a + e * a + e * b) := by
  intros
  have h : (0 : ℝ) ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)) - (2 * (a * b + a * c + b * c + b * d + c * d + c * e + d * e + d * a + e * a + e * b)) := by
    calc
      0 ≤ (1 : ℝ) * ((e + ((-1) * d)))^2 + (1 : ℝ) * ((e + ((-1) * c)))^2 + (1 : ℝ) * ((e + ((-1) * b)))^2 + (1 : ℝ) * ((e + ((-1) * a)))^2 + (1 : ℝ) * ((d + ((-1) * c)))^2 + (1 : ℝ) * ((d + ((-1) * b)))^2 + (1 : ℝ) * ((d + ((-1) * a)))^2 + (1 : ℝ) * ((c + ((-1) * b)))^2 + (1 : ℝ) * ((c + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)) - (2 * (a * b + a * c + b * c + b * d + c * d + c * e + d * e + d * a + e * a + e * b)) := by ring
  exact sub_nonneg.mp h
