-- Prove2me | solution 1 for lean_workbook_plus_43561
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:04:40.743337+00:00
-- url     : https://prove2.me/submissions/bdaa24b4-10c1-426b-97b5-46871b67eb66

import Mathlib

set_option autoImplicit false

namespace OrderedPolynomialRange

noncomputable def value (x y : ℝ) : ℝ :=
  (y ^ 3 - y ^ 2) * x ^ 3 + x ^ 2 - (y ^ 2 + 1) * x + y

noncomputable def remainder (x y : ℝ) : ℝ :=
  y ^ 2 * (x - 1) * (x + 2) + (y - 1) * (3 * y + 2) + 1

theorem gap_identity (x y : ℝ) :
    value x y - ((x - 1) ^ 2 + (y - 1) ^ 2) =
      (y - 1) * ((y - 1) ^ 2 + (x - 1) * remainder x y) := by
  unfold value remainder
  ring

theorem remainder_pos {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    0 < remainder x y := by
  unfold remainder
  have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hy1 : 0 ≤ y - 1 := sub_nonneg.mpr hy
  have hp : 0 ≤ y ^ 2 * (x - 1) * (x + 2) := by positivity
  have hq : 0 ≤ (y - 1) * (3 * y + 2) := by positivity
  linarith

theorem quadratic_lower_bound {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (x - 1) ^ 2 + (y - 1) ^ 2 ≤ value x y := by
  have hr := le_of_lt (remainder_pos hx hy)
  have hg := gap_identity x y
  have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hy1 : 0 ≤ y - 1 := sub_nonneg.mpr hy
  have hn : 0 ≤ (y - 1) * ((y - 1) ^ 2 + (x - 1) * remainder x y) := by
    positivity
  linarith

theorem nonneg {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 0 ≤ value x y := by
  have h := quadratic_lower_bound hx hy
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]

theorem lower_bound_equality_iff {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    value x y = (x - 1) ^ 2 + (y - 1) ^ 2 ↔ y = 1 := by
  constructor
  · intro he
    by_contra hy1
    have hp : 0 < y - 1 := by rcases lt_or_eq_of_le hy with h | h <;> aesop
    have hs : 0 < (y - 1) ^ 2 := sq_pos_of_pos hp
    have hr := le_of_lt (remainder_pos hx hy)
    have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
    have hn : 0 ≤ (x - 1) * remainder x y := by positivity
    have hprod : 0 < (y - 1) * ((y - 1) ^ 2 + (x - 1) * remainder x y) :=
      mul_pos hp (by linarith)
    have hg := gap_identity x y
    linarith
  · rintro rfl
    simp [value]
    ring

theorem zero_iff {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    value x y = 0 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro hz
    have h := quadratic_lower_bound hx hy
    have hx0 : (x - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (y - 1)]
    have hy0 : (y - 1) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 1)]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hx0),
      sub_eq_zero.mp (sq_eq_zero_iff.mp hy0)⟩
  · rintro ⟨rfl, rfl⟩
    unfold value
    ring

theorem positive_iff {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    0 < value x y ↔ x ≠ 1 ∨ y ≠ 1 := by
  rw [lt_iff_le_and_ne]
  simp only [nonneg hx hy, true_and, ne_eq, eq_comm (a := (0 : ℝ)),
    zero_iff hx hy, not_and_or]

theorem boundary_value (x : ℝ) : value x 1 = (x - 1) ^ 2 := by
  unfold value
  ring

theorem realizes_nonnegative {v : ℝ} (hv : 0 ≤ v) :
    1 ≤ 1 + Real.sqrt v ∧ value (1 + Real.sqrt v) 1 = v := by
  constructor
  · exact le_add_of_nonneg_right (Real.sqrt_nonneg v)
  · rw [boundary_value]
    simpa using Real.sq_sqrt hv

theorem range_exact :
    {v : ℝ | ∃ x y : ℝ, 1 ≤ x ∧ 1 ≤ y ∧ value x y = v} = Set.Ici 0 := by
  ext v
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact nonneg hx hy
  · intro hv
    exact ⟨1 + Real.sqrt v, 1, (realizes_nonnegative hv).1, le_rfl,
      (realizes_nonnegative hv).2⟩

theorem best_quadratic_coefficient (k : ℝ) :
    (∀ x y : ℝ, 1 ≤ x → 1 ≤ y →
      k * ((x - 1) ^ 2 + (y - 1) ^ 2) ≤ value x y) ↔ k ≤ 1 := by
  constructor
  · intro h
    have he := h 2 1 (by norm_num) le_rfl
    have hs : ((2 : ℝ) - 1) ^ 2 + (1 - 1) ^ 2 = 1 := by ring
    have hv : value 2 1 = 1 := by unfold value; ring
    rw [hs, hv, mul_one] at he
    exact he
  · intro hk x y hx hy
    calc
      k * ((x - 1) ^ 2 + (y - 1) ^ 2) ≤
          1 * ((x - 1) ^ 2 + (y - 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ value x y := by simpa only [one_mul] using quadratic_lower_bound hx hy

theorem ratio_substitution_bound {a b c : ℝ}
    (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) : 0 ≤ value (a / b) (b / c) := by
  have hb : 0 < b := lt_of_lt_of_le hc hbc
  exact nonneg ((one_le_div hb).2 hab) ((one_le_div hc).2 hbc)

theorem ratio_substitution_equality {a b c : ℝ}
    (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 < c) :
    value (a / b) (b / c) = 0 ↔ a = b ∧ b = c := by
  have hb : 0 < b := lt_of_lt_of_le hc hbc
  rw [zero_iff ((one_le_div hb).2 hab) ((one_le_div hc).2 hbc),
    div_eq_one_iff_eq (ne_of_gt hb), div_eq_one_iff_eq (ne_of_gt hc)]

end OrderedPolynomialRange

theorem solution (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    (y ^ 3 - y ^ 2) * x ^ 3 + x ^ 2 - (y ^ 2 + 1) * x + y ≥ 0 := by
  exact OrderedPolynomialRange.nonneg hx hy

#print axioms OrderedPolynomialRange.gap_identity
#print axioms OrderedPolynomialRange.remainder_pos
#print axioms OrderedPolynomialRange.quadratic_lower_bound
#print axioms OrderedPolynomialRange.nonneg
#print axioms OrderedPolynomialRange.lower_bound_equality_iff
#print axioms OrderedPolynomialRange.zero_iff
#print axioms OrderedPolynomialRange.positive_iff
#print axioms OrderedPolynomialRange.boundary_value
#print axioms OrderedPolynomialRange.realizes_nonnegative
#print axioms OrderedPolynomialRange.range_exact
#print axioms OrderedPolynomialRange.best_quadratic_coefficient
#print axioms OrderedPolynomialRange.ratio_substitution_bound
#print axioms OrderedPolynomialRange.ratio_substitution_equality
#print axioms solution
