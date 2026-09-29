-- Prove2me | solution 1 for lean_workbook_plus_48848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:58:27.24731+00:00
-- url     : https://prove2.me/submissions/1e5e4aa2-75e0-4b55-ab91-c5f67d83f193

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1) (k : ℝ) (hk : k ≥ 1) : a / (b + 1) + k * b / (a + 1) ≤ k := by
  have sourceBound (u v : ℝ) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) : u/(v+1)+v/(u+1) ≤ 1 := by
    have hdu : 0 < u+1 := by positivity
    have hdv : 0 < v+1 := by positivity
    have hp := mul_nonneg (show 0 ≤ 1-u by linarith) (show 0 ≤ 1+u-v by linarith)
    have hq := mul_nonneg hv0 (show 0 ≤ 1-v by linarith)
    have hn : 0 ≤ 1+u*v-u^2-v^2 := by nlinarith
    have he : 1-(u/(v+1)+v/(u+1)) = (1+u*v-u^2-v^2)/((u+1)*(v+1)) := by
      field_simp [ne_of_gt hdu, ne_of_gt hdv]
      <;> ring
    have hpos := div_nonneg hn (le_of_lt (mul_pos hdu hdv))
    linarith
  have ha1 : a ≤ 1 := by linarith [hab.2.1, hab.2.2]
  have hb1 : b ≤ 1 := by linarith [hab.1, hab.2.2]
  have hbase := sourceBound a b hab.1 hab.2.1 ha1 hb1
  have hA : 0 ≤ a/(b+1) := div_nonneg hab.1 (by linarith [hab.2.1])
  have hk0 : 0 ≤ k := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase hk0
  have hweight := mul_nonneg (show 0 ≤ k-1 by linarith) hA
  simp only [mul_add, mul_div_assoc, mul_one] at hscaled hweight
  rw [mul_div_assoc]
  nlinarith
