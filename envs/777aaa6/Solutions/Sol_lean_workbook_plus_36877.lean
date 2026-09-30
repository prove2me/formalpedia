-- Prove2me | solution 1 for lean_workbook_plus_36877
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:00:06.86758+00:00
-- url     : https://prove2.me/submissions/7edfcb7c-34d3-4077-b4b4-96e5afc45e70

import Mathlib

set_option autoImplicit false

namespace RationalSquareGapInequality

noncomputable section

def left (x y : ℝ) : ℝ := 3 * x / (4 * (x + 2 * y)) + 3 / 4

def right (x y : ℝ) : ℝ := (2 * x + 4 * y) / (x + 5 * y)

theorem gap_identity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    right x y - left x y =
      (x - y) ^ 2 / (2 * (x + 2 * y) * (x + 5 * y)) := by
  unfold left right
  have h2 : x + 2 * y ≠ 0 := ne_of_gt (by positivity)
  have h5 : x + 5 * y ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem source_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    left x y ≤ right x y := by
  have h := gap_identity hx hy
  have hn : 0 ≤ (x - y) ^ 2 / (2 * (x + 2 * y) * (x + 5 * y)) := by positivity
  linarith

theorem source_equality_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    left x y = right x y ↔ x = y := by
  have hd : 0 < 2 * (x + 2 * y) * (x + 5 * y) := by positivity
  rw [eq_comm, ← sub_eq_zero, gap_identity hx hy,
    div_eq_zero_iff, or_iff_left (ne_of_gt hd), sq_eq_zero_iff, sub_eq_zero]

theorem strict_source_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    left x y < right x y ↔ x ≠ y := by
  constructor
  · intro h he
    exact (ne_of_lt h) ((source_equality_iff hx hy).2 he)
  · intro h
    exact lt_of_le_of_ne (source_bound hx hy)
      (fun he => h ((source_equality_iff hx hy).1 he))

theorem left_as_coefficient {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    left x y = (3 / 4) * (x / (x + 2 * y) + 1) := by
  unfold left
  have h2 : x + 2 * y ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem best_coefficient_iff (k : ℝ) :
    (∀ x y : ℝ, 0 < x → 0 < y →
      k * (x / (x + 2 * y) + 1) ≤ right x y) ↔ k ≤ 3 / 4 := by
  constructor
  · intro h
    have h1 : k * (4 / 3) ≤ 1 := by
      convert h 1 1 (by norm_num) (by norm_num) using 1 <;> norm_num [right]
      rfl
    linarith only [h1]
  · intro hk x y hx hy
    have hp : 0 ≤ x / (x + 2 * y) + 1 := by positivity
    calc
      k * (x / (x + 2 * y) + 1) ≤
          (3 / 4) * (x / (x + 2 * y) + 1) := mul_le_mul_of_nonneg_right hk hp
      _ = left x y := (left_as_coefficient hx hy).symm
      _ ≤ right x y := source_bound hx hy

theorem greatest_coefficient :
    IsGreatest {k : ℝ | ∀ x y : ℝ, 0 < x → 0 < y →
      k * (x / (x + 2 * y) + 1) ≤ right x y} (3 / 4) := by
  exact ⟨(best_coefficient_iff _).2 le_rfl,
    fun k hk => (best_coefficient_iff k).1 hk⟩

theorem normalized_posted_gap {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    2 * x + 4 * y / (x + 5 * y) - right x y = 8 * x * y / (x + 5 * y) := by
  unfold right
  have h5 : x + 5 * y ≠ 0 := ne_of_gt (by positivity)
  field_simp
  nlinarith [hxy]

theorem normalized_posted_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    left x y < 2 * x + 4 * y / (x + 5 * y) := by
  have hg := normalized_posted_gap hx hy hxy
  have hp : 0 < 8 * x * y / (x + 5 * y) := by positivity
  have hs := source_bound hx hy
  linarith

theorem square_sum_eq_pair_sum_iff (a b c : ℝ) :
    a ^ 2 + b ^ 2 + c ^ 2 = a * b + b * c + c * a ↔ a = b ∧ b = c := by
  constructor
  · intro h
    have h1 := sq_nonneg (a - b)
    have h2 := sq_nonneg (b - c)
    have h3 := sq_nonneg (c - a)
    have hab : (a - b) ^ 2 = 0 := by nlinarith
    have hbc : (b - c) ^ 2 = 0 := by nlinarith
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hab),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hbc)⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem quadratic_substitution_bound {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    left (a ^ 2 + b ^ 2 + c ^ 2) (a * b + b * c + c * a) ≤
      right (a ^ 2 + b ^ 2 + c ^ 2) (a * b + b * c + c * a) := by
  apply source_bound <;> positivity

theorem quadratic_substitution_equality_iff {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    left (a ^ 2 + b ^ 2 + c ^ 2) (a * b + b * c + c * a) =
      right (a ^ 2 + b ^ 2 + c ^ 2) (a * b + b * c + c * a) ↔ a = b ∧ b = c := by
  rw [source_equality_iff (by positivity) (by positivity), square_sum_eq_pair_sum_iff]

end

end RationalSquareGapInequality

theorem solution {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    3 * x / (4 * (x + 2 * y)) + 3 / 4 ≤ 2 * x + 4 * y / (x + 5 * y) := by
  exact le_of_lt (RationalSquareGapInequality.normalized_posted_strict hx hy hxy)

#print axioms RationalSquareGapInequality.gap_identity
#print axioms RationalSquareGapInequality.source_bound
#print axioms RationalSquareGapInequality.source_equality_iff
#print axioms RationalSquareGapInequality.strict_source_iff
#print axioms RationalSquareGapInequality.left_as_coefficient
#print axioms RationalSquareGapInequality.best_coefficient_iff
#print axioms RationalSquareGapInequality.greatest_coefficient
#print axioms RationalSquareGapInequality.normalized_posted_gap
#print axioms RationalSquareGapInequality.normalized_posted_strict
#print axioms RationalSquareGapInequality.square_sum_eq_pair_sum_iff
#print axioms RationalSquareGapInequality.quadratic_substitution_bound
#print axioms RationalSquareGapInequality.quadratic_substitution_equality_iff
#print axioms solution
