-- Prove2me | solution 1 for lean_workbook_plus_42693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:16.999074+00:00
-- url     : https://prove2.me/submissions/056d7a4e-9a12-48d3-86a6-cec697c9085b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) : 8 + a * b * c + b * c * d + c * d * a + d * a * b ≥ 3 * (a + b + c + d) := by
  have hu : 0 ≤ a-1 := by linarith
  have hv : 0 ≤ b-1 := by linarith
  have hw : 0 ≤ c-1 := by linarith
  have ht : 0 ≤ d-1 := by linarith
  have h1 := mul_nonneg hu hv
  have h2 := mul_nonneg hu hw
  have h3 := mul_nonneg hu ht
  have h4 := mul_nonneg hv hw
  have h5 := mul_nonneg hv ht
  have h6 := mul_nonneg hw ht
  have h7 := mul_nonneg h1 hw
  have h8 := mul_nonneg h1 ht
  have h9 := mul_nonneg h2 ht
  have h10 := mul_nonneg h4 ht
  nlinarith
