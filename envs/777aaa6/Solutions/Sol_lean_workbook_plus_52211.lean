-- Prove2me | solution 1 for lean_workbook_plus_52211
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:34:33.356837+00:00
-- url     : https://prove2.me/submissions/509dc1b2-78ca-40e8-8f25-2b33e72e1afc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem reciprocal_quadratics_gap (x y : ℝ) (h : 1 + x * y ≠ 0) :
    1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) - 2 / (1 + x * y) =
      ((x * y - 1) * (x - y) ^ 2) / ((x ^ 2 + 1) * (y ^ 2 + 1) * (1 + x * y)) := by
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  have hy : y ^ 2 + 1 ≠ 0 := by positivity
  field_simp [hx, hy, h]
  <;> ring

theorem reciprocal_quadratics_equality (x y : ℝ) (h : 1 ≤ x * y) :
    1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) = 2 / (1 + x * y) ↔ x * y = 1 ∨ x = y := by
  have hxy : 0 < 1 + x * y := by linarith
  have hd : (x ^ 2 + 1) * (y ^ 2 + 1) * (1 + x * y) ≠ 0 := by positivity
  have hi := reciprocal_quadratics_gap x y hxy.ne'
  constructor
  · intro he
    have hg : ((x * y - 1) * (x - y) ^ 2) /
        ((x ^ 2 + 1) * (y ^ 2 + 1) * (1 + x * y)) = 0 := by linarith only [hi, he]
    have hn := (div_eq_iff hd).mp hg
    simp only [zero_mul] at hn
    rcases mul_eq_zero.mp hn with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by nlinarith)
  · intro he
    have hn : (x * y - 1) * (x - y) ^ 2 = 0 := by
      rcases he with he | he
      · rw [he]
        ring
      · rw [he]
        ring
    rw [hn, zero_div] at hi
    exact sub_eq_zero.mp hi

theorem solution (x y : ℝ) (h : x * y ≥ 1) :
    1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) ≥ 2 / (1 + x * y) := by
  have hxy : 0 < 1 + x * y := by linarith
  have hn := mul_nonneg (show 0 ≤ x * y - 1 by linarith) (sq_nonneg (x - y))
  have hd : 0 < (x ^ 2 + 1) * (y ^ 2 + 1) * (1 + x * y) := by positivity
  have hg := div_nonneg hn hd.le
  rw [← reciprocal_quadratics_gap x y hxy.ne'] at hg
  exact sub_nonneg.mp hg

#print axioms solution
#print axioms reciprocal_quadratics_equality
