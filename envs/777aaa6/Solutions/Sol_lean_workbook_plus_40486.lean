-- Prove2me | solution 1 for lean_workbook_plus_40486
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:45:21.736334+00:00
-- url     : https://prove2.me/submissions/c6190c10-8303-4c5a-9048-d84c7a7d0ce5

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace QuadraticReciprocalConstraint

def gap (u v w : ℝ) : ℝ := u * v * w - 2 * (u * v + v * w + w * u) + 5

def value (a b c : ℝ) : ℝ := 1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2)

-- The weighted-square Schur identity is a disclosed shared ingredient.
theorem schur_nonnegative {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hs : u + v + w = 3) :
    0 ≤ (u + v + w) ^ 3 + 9 * u * v * w -
      4 * (u + v + w) * (u * v + v * w + w * u) := by
  have hp : 0 < u + (v + w) / 4 := by linarith
  have hi : (u + (v + w) / 4) *
      ((u + v + w) ^ 3 + 9 * u * v * w -
        4 * (u + v + w) * (u * v + v * w + w * u)) =
      v * w * (v - w) ^ 2 +
      (w * u * (w - u) ^ 2 + u * v * (u - v) ^ 2) / 4 +
      (2 * u ^ 2 - v ^ 2 - w ^ 2 - u * v + 2 * v * w - w * u) ^ 2 / 4 := by ring
  have hn : 0 ≤ (u + (v + w) / 4) *
      ((u + v + w) ^ 3 + 9 * u * v * w -
        4 * (u + v + w) * (u * v + v * w + w * u)) := by
    rw [hi]
    positivity
  exact nonneg_of_mul_nonneg_right hn hp

theorem pair_nonpos_two {u v w : ℝ} (hs : u + v + w = 3)
    (hu : u ≤ 0) (hv : v ≤ 0) : u * v + v * w + w * u ≤ 0 := by
  have hw : w = 3 - u - v := by linarith
  rw [hw]
  nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg_of_nonpos_of_nonpos hu hv]

theorem pair_nonpos_one {u v w : ℝ} (hu : u < 0) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hr : 0 ≤ u * v * w) : u * v + v * w + w * u ≤ 0 := by
  have hz : v * w = 0 := by
    by_contra hn
    have hp : 0 < v * w := lt_of_le_of_ne (mul_nonneg hv hw) (Ne.symm hn)
    have hh := mul_neg_of_neg_of_pos hu hp
    nlinarith only [hh, hr]
  rw [hz, add_zero]
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg hu.le hv)
    (mul_nonpos_of_nonneg_of_nonpos hw hu.le)

theorem signed_schur {u v w : ℝ} (hs : u + v + w = 3)
    (hr : 0 ≤ u * v * w) :
    0 ≤ 27 + 9 * u * v * w - 12 * (u * v + v * w + w * u) := by
  by_cases hu : 0 ≤ u
  · by_cases hv : 0 ≤ v
    · by_cases hw : 0 ≤ w
      · have hh := schur_nonnegative hu hv hw hs
        rw [hs] at hh
        nlinarith only [hh]
      · have hp := pair_nonpos_one (lt_of_not_ge hw) hu hv
          (show 0 ≤ w * u * v by nlinarith only [hr])
        nlinarith only [hp, hr]
    · by_cases hw : 0 ≤ w
      · have hp := pair_nonpos_one (lt_of_not_ge hv) hu hw
          (show 0 ≤ v * u * w by nlinarith only [hr])
        nlinarith only [hp, hr]
      · have hp := pair_nonpos_two (show v + w + u = 3 by linarith)
          (le_of_not_ge hv) (le_of_not_ge hw)
        nlinarith only [hp, hr]
  · by_cases hv : 0 ≤ v
    · by_cases hw : 0 ≤ w
      · have hp := pair_nonpos_one (lt_of_not_ge hu) hv hw hr
        nlinarith only [hp, hr]
      · have hp := pair_nonpos_two (show u + w + v = 3 by linarith)
          (le_of_not_ge hu) (le_of_not_ge hw)
        nlinarith only [hp, hr]
    · have hp := pair_nonpos_two hs (le_of_not_ge hu) (le_of_not_ge hv)
      nlinarith only [hp, hr]

theorem gap_refinement {u v w : ℝ} (hs : u + v + w = 3)
    (hr : 0 ≤ u * v * w) :
    (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 ≤ 9 * gap u v w := by
  have hh := signed_schur hs hr
  have hs2 : (u + v + w) ^ 2 = 9 := by rw [hs]; norm_num
  unfold gap
  nlinarith only [hh, hs2]

theorem gap_nonnegative {u v w : ℝ} (hs : u + v + w = 3)
    (hr : 0 ≤ u * v * w) : 0 ≤ gap u v w := by
  have hh := gap_refinement hs hr
  nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]

theorem gap_zero_iff {u v w : ℝ} (hs : u + v + w = 3)
    (hr : 0 ≤ u * v * w) : gap u v w = 0 ↔ u = 1 ∧ v = 1 ∧ w = 1 := by
  constructor
  · intro hz
    have hh := gap_refinement hs hr
    have huv : (u - v) ^ 2 = 0 := by
      nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]
    have hvw : (v - w) ^ 2 = 0 := by
      nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]
    have he1 : u = v := by nlinarith only [huv]
    have he2 : v = w := by nlinarith only [hvw]
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [gap]
    rfl

theorem gap_identity {a b c : ℝ} (h : a * b + b * c + c * a = 3) :
    (1 - value a b c) * ((a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2)) =
      gap (a * b) (b * c) (c * a) := by
  have ha : a ^ 2 + 2 ≠ 0 := by positivity
  have hb : b ^ 2 + 2 ≠ 0 := by positivity
  have hc : c ^ 2 + 2 ≠ 0 := by positivity
  have h2 : (a * b + b * c + c * a) ^ 2 = 9 := by rw [h]; norm_num
  unfold value gap
  field_simp
  nlinarith only [h2]

theorem source_bound {a b c : ℝ} (h : a * b + b * c + c * a = 3) :
    value a b c ≤ 1 := by
  have hr : 0 ≤ (a * b) * (b * c) * (c * a) := by
    nlinarith only [sq_nonneg (a * b * c)]
  have hg := gap_nonnegative h hr
  have hi := gap_identity h
  have hd : 0 < (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) := by positivity
  have hn : 0 ≤ 1 - value a b c := nonneg_of_mul_nonneg_right (by linarith) hd
  linarith

theorem equality_iff {a b c : ℝ} (h : a * b + b * c + c * a = 3) :
    value a b c = 1 ↔ (a = 1 ∧ b = 1 ∧ c = 1) ∨
      (a = -1 ∧ b = -1 ∧ c = -1) := by
  constructor
  · intro he
    have hr : 0 ≤ (a * b) * (b * c) * (c * a) := by
      nlinarith only [sq_nonneg (a * b * c)]
    have hz : gap (a * b) (b * c) (c * a) = 0 := by
      have hi := gap_identity h
      rw [he] at hi
      nlinarith only [hi]
    obtain ⟨hab, hbc, hca⟩ := (gap_zero_iff h hr).mp hz
    have hc : c ≠ 0 := by intro hc; rw [hc] at hbc; norm_num at hbc
    have ha : a ≠ 0 := by intro ha; rw [ha] at hab; norm_num at hab
    have hab' : a = b := by
      apply (mul_right_cancel₀ hc)
      nlinarith only [hbc, hca]
    have hbc' : b = c := by
      apply (mul_left_cancel₀ ha)
      nlinarith only [hab, hca]
    have ha2 : a * a = 1 := by simpa only [← hab'] using hab
    have hz' : (a - 1) * (a + 1) = 0 := by nlinarith only [ha2]
    rcases mul_eq_zero.mp hz' with hp | hn
    · left; exact ⟨by linarith, by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num [value] <;> rfl

theorem positive_value (a b c : ℝ) : 0 < value a b c := by
  unfold value
  positivity

theorem upper_constant_iff (k : ℝ) :
    (∀ a b c : ℝ, a * b + b * c + c * a = 3 → value a b c ≤ k) ↔ 1 ≤ k := by
  constructor
  · intro hk
    have hh := hk 1 1 1 (by norm_num)
    norm_num [value] at hh
    exact hh
  · intro hk a b c h
    exact (source_bound h).trans hk

theorem shifted_bound {a b c k : ℝ} (h : a * b + b * c + c * a = 3)
    (hk : 2 ≤ k) : 1 / (a ^ 2 + k) + 1 / (b ^ 2 + k) + 1 / (c ^ 2 + k) ≤ 1 := by
  have ha := one_div_le_one_div_of_le (show 0 < a ^ 2 + 2 by positivity)
    (show a ^ 2 + 2 ≤ a ^ 2 + k by linarith)
  have hb := one_div_le_one_div_of_le (show 0 < b ^ 2 + 2 by positivity)
    (show b ^ 2 + 2 ≤ b ^ 2 + k by linarith)
  have hc := one_div_le_one_div_of_le (show 0 < c ^ 2 + 2 by positivity)
    (show c ^ 2 + 2 ≤ c ^ 2 + k by linarith)
  have hh := source_bound h
  unfold value at hh
  linarith only [ha, hb, hc, hh]

theorem shift_criterion {k : ℝ} (hk : 0 < k) :
    (∀ a b c : ℝ, a * b + b * c + c * a = 3 →
      1 / (a ^ 2 + k) + 1 / (b ^ 2 + k) + 1 / (c ^ 2 + k) ≤ 1) ↔ 2 ≤ k := by
  constructor
  · intro hh
    have ht := hh 1 1 1 (by norm_num)
    norm_num only [one_pow] at ht
    have he : 1 / (1 + k) + 1 / (1 + k) + 1 / (1 + k) = 3 / (1 + k) := by ring
    rw [he] at ht
    have hp : 0 < 1 + k := by linarith
    have hb := (div_le_iff₀ hp).mp ht
    linarith
  · intro hh a b c h
    exact shifted_bound h hh

end QuadraticReciprocalConstraint

theorem solution (a b c : ℝ) (h : a * b + b * c + c * a = 3) :
    1 / (a ^ 2 + 2) + 1 / (b ^ 2 + 2) + 1 / (c ^ 2 + 2) ≤ 1 :=
  QuadraticReciprocalConstraint.source_bound h

#print axioms QuadraticReciprocalConstraint.gap
#print axioms QuadraticReciprocalConstraint.value
#print axioms QuadraticReciprocalConstraint.schur_nonnegative
#print axioms QuadraticReciprocalConstraint.pair_nonpos_two
#print axioms QuadraticReciprocalConstraint.pair_nonpos_one
#print axioms QuadraticReciprocalConstraint.signed_schur
#print axioms QuadraticReciprocalConstraint.gap_refinement
#print axioms QuadraticReciprocalConstraint.gap_nonnegative
#print axioms QuadraticReciprocalConstraint.gap_zero_iff
#print axioms QuadraticReciprocalConstraint.gap_identity
#print axioms QuadraticReciprocalConstraint.source_bound
#print axioms QuadraticReciprocalConstraint.equality_iff
#print axioms QuadraticReciprocalConstraint.positive_value
#print axioms QuadraticReciprocalConstraint.upper_constant_iff
#print axioms QuadraticReciprocalConstraint.shifted_bound
#print axioms QuadraticReciprocalConstraint.shift_criterion
#print axioms solution
