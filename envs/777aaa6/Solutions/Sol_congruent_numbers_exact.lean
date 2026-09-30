-- Prove2me | solution 1 for congruent_numbers_exact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:28.707172+00:00
-- url     : https://prove2.me/submissions/1af4ae60-8275-49a0-a408-627a9a225b85

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private theorem triangle_to_curve (n a b c : ℚ) (hn : 0 < n) (hb : 0 < b)
    (htriangle : a ^ 2 + b ^ 2 = c ^ 2) (harea : a * b / 2 = n) :
    ∃ x y : ℚ, y ^ 2 = x ^ 3 - n ^ 2 * x ∧ y ≠ 0 := by
  have hden : c - a ≠ 0 := by
    intro h
    have hca : c = a := sub_eq_zero.mp h
    rw [hca] at htriangle
    nlinarith
  refine ⟨n * b / (c - a), 2 * n ^ 2 / (c - a), ?_, ?_⟩
  · have hab : a * b = 2 * n := by linarith
    field_simp
    linear_combination -b * htriangle - 2 * (c - a) * hab
  · exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt hn))) hden

private theorem curve_to_triangle (n x y : ℚ) (hn : 0 < n)
    (hcurve : y ^ 2 = x ^ 3 - n ^ 2 * x) (hy : y ≠ 0) :
    ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n := by
  let a := (x ^ 2 - n ^ 2) / y
  let b := 2 * n * x / y
  let c := (x ^ 2 + n ^ 2) / y
  have htriangle : a ^ 2 + b ^ 2 = c ^ 2 := by
    dsimp [a, b, c]
    field_simp
    ring
  have harea : a * b / 2 = n := by
    dsimp [a, b]
    calc
      (x ^ 2 - n ^ 2) / y * (2 * n * x / y) / 2 =
          n * (x ^ 3 - n ^ 2 * x) / y ^ 2 := by ring
      _ = n := by rw [← hcurve]; field_simp
  have hpos : 0 < a * b := by linarith
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hpos)).1
  have hb : b ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hpos)).2
  refine ⟨|a|, |b|, c, abs_pos.mpr ha, abs_pos.mpr hb, ?_, ?_⟩
  · simpa only [sq_abs] using htriangle
  · rw [← abs_mul, abs_of_pos hpos]
    exact harea

theorem solution :
    ∀ n : ℕ, 1 ≤ n →
    ((∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
      a * b / 2 = n) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x ∧ y ≠ 0)) := by
  intro n hn
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  constructor
  · rintro ⟨a, b, c, _, hb, htriangle, harea⟩
    exact triangle_to_curve n a b c hnq hb htriangle harea
  · rintro ⟨x, y, hcurve, hy⟩
    exact curve_to_triangle n x y hnq hcurve hy

#print axioms solution
