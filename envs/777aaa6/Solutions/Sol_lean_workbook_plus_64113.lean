-- Prove2me | solution 1 for lean_workbook_plus_64113
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:27:38.094157+00:00
-- url     : https://prove2.me/submissions/d215715c-9b14-454d-8d58-74397e1b2d02

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem reciprocal_cubes_product_sharp (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h : 1 / (a ^ 3 + 1) + 1 / (b ^ 3 + 1) + 1 / (c ^ 3 + 1) = 1) :
    2 ≤ a * b * c ∧ (a * b * c = 2 ↔ a = b ∧ b = c) := by
  have hda : a ^ 3 + 1 ≠ 0 := by positivity
  have hdb : b ^ 3 + 1 ≠ 0 := by positivity
  have hdc : c ^ 3 + 1 ≠ 0 := by positivity
  have he : (a * b * c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + 2 := by
    have hh := h
    field_simp [hda, hdb, hdc] at hh
    nlinarith only [hh]
  have hs : 0 < a + b + c := by positivity
  have ht : 0 < a * b * c := by positivity
  have hi : 2 * (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) =
      (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by ring
  have hsq : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
  have hg : 0 ≤ a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c := by
    have := mul_nonneg hs.le hsq
    linarith only [hi, this]
  have hp : 0 ≤ (a * b * c - 2) * (a * b * c + 1) ^ 2 := by
    nlinarith only [he, hg]
  have htp : 0 < (a * b * c + 1) ^ 2 := by positivity
  have hl : 2 ≤ a * b * c := by
    have := nonneg_of_mul_nonneg_left hp htp
    linarith
  refine ⟨hl, ?_⟩
  constructor
  · intro ht2
    rw [ht2] at he
    have hmul : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) = 0 := by
      nlinarith only [hi, he, ht2]
    have hz := (mul_eq_zero.mp hmul).resolve_left hs.ne'
    constructor <;> nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · rintro ⟨rfl, rfl⟩
    field_simp [hdc] at h
    nlinarith only [h]

theorem reciprocal_cubes_product_attained :
    ∃ r : ℝ, 0 < r ∧
      (1 / (r ^ 3 + 1) + 1 / (r ^ 3 + 1) + 1 / (r ^ 3 + 1) = 1) ∧ r * r * r = 2 := by
  let r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr3 : r ^ 3 = 2 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  refine ⟨r, hr, ?_, ?_⟩
  · rw [hr3]
    norm_num
  · nlinarith only [hr3]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1)
    (h : 1 / (a ^ 3 + 1) + 1 / (b ^ 3 + 1) + 1 / (c ^ 3 + 1) = 1) : a * b * c ≥ 2 :=
  (reciprocal_cubes_product_sharp a b c ha hb hc h).1

#print axioms solution
#print axioms reciprocal_cubes_product_sharp
#print axioms reciprocal_cubes_product_attained
