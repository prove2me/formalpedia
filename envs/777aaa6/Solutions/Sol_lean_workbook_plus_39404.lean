-- Prove2me | solution 1 for lean_workbook_plus_39404
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:35:52.239893+00:00
-- url     : https://prove2.me/submissions/13bbfb70-3aeb-426a-a76f-2d2ece57574b

import Mathlib

namespace UnitCircleQuarticExtrema

def value (x y : ℝ) : ℝ := x * y * (y ^ 2 - x ^ 2)

def attainable : Set ℝ := {v | ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ value x y = v}

theorem gap_identities (x y : ℝ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * value x y = (y ^ 2 - x ^ 2 - 2 * x * y) ^ 2 ∧
    (x ^ 2 + y ^ 2) ^ 2 + 4 * value x y = (y ^ 2 - x ^ 2 + 2 * x * y) ^ 2 := by
  unfold value
  constructor <;> ring

theorem homogeneous_bounds (x y : ℝ) :
    -((x ^ 2 + y ^ 2) ^ 2 / 4) ≤ value x y ∧
      value x y ≤ (x ^ 2 + y ^ 2) ^ 2 / 4 := by
  obtain ⟨hu, hl⟩ := gap_identities x y
  constructor
  · nlinarith only [hl, sq_nonneg (y ^ 2 - x ^ 2 + 2 * x * y)]
  · nlinarith only [hu, sq_nonneg (y ^ 2 - x ^ 2 - 2 * x * y)]

theorem sharp_bounds (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    -(1 / 4) ≤ value x y ∧ value x y ≤ 1 / 4 := by
  simpa only [h, one_pow] using homogeneous_bounds x y

theorem upper_equality (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    value x y = 1 / 4 ↔ y ^ 2 - x ^ 2 = 2 * x * y := by
  have hg := (gap_identities x y).1
  rw [h, one_pow] at hg
  constructor
  · intro hv
    have hz : (y ^ 2 - x ^ 2 - 2 * x * y) ^ 2 = 0 := by linarith only [hg, hv]
    have he := sq_eq_zero_iff.mp hz
    linarith
  · intro he
    have hz : y ^ 2 - x ^ 2 - 2 * x * y = 0 := by linarith
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hg
    linarith

theorem lower_equality (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    value x y = -(1 / 4) ↔ y ^ 2 - x ^ 2 = -2 * x * y := by
  have hg := (gap_identities x y).2
  rw [h, one_pow] at hg
  constructor
  · intro hv
    have hz : (y ^ 2 - x ^ 2 + 2 * x * y) ^ 2 = 0 := by linarith only [hg, hv]
    have he := sq_eq_zero_iff.mp hz
    linarith
  · intro he
    have hz : y ^ 2 - x ^ 2 + 2 * x * y = 0 := by linarith
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hg
    linarith

theorem extremizers : ∃ x y : ℝ,
    x ^ 2 + y ^ 2 = 1 ∧ value x y = 1 / 4 ∧
    (-x) ^ 2 + y ^ 2 = 1 ∧ value (-x) y = -(1 / 4) := by
  let r := Real.sqrt 2
  let x := Real.sqrt ((2 - r) / 4)
  let y := (1 + r) * x
  have hr : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 2
  have hr2 : r < 2 := by nlinarith only [hr, hr0]
  have hx : x ^ 2 = (2 - r) / 4 := Real.sq_sqrt (by linarith)
  have hy : y ^ 2 = (2 + r) / 4 := by
    dsimp [y]
    rw [mul_pow, hx]
    linear_combination -(r / 4) * hr
  have hc : x ^ 2 + y ^ 2 = 1 := by linarith only [hx, hy]
  have he : y ^ 2 - x ^ 2 = 2 * x * y := by
    dsimp only [y]
    linear_combination x ^ 2 * hr
  have hv := (upper_equality x y hc).mpr he
  refine ⟨x, y, hc, hv, by simpa only [neg_sq] using hc, ?_⟩
  unfold value at hv ⊢
  nlinarith only [hv]

theorem maximum : IsGreatest attainable (1 / 4) := by
  obtain ⟨x, y, hc, hv, _, _⟩ := extremizers
  refine ⟨⟨x, y, hc, hv⟩, ?_⟩
  rintro v ⟨a, b, h, he⟩
  rw [← he]
  exact (sharp_bounds a b h).2

theorem minimum : IsLeast attainable (-(1 / 4)) := by
  obtain ⟨x, y, _, _, hc, hv⟩ := extremizers
  refine ⟨⟨-x, y, hc, hv⟩, ?_⟩
  rintro v ⟨a, b, h, he⟩
  rw [← he]
  exact (sharp_bounds a b h).1

end UnitCircleQuarticExtrema

theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    -1 ≤ x * y * (y ^ 2 - x ^ 2) ∧ x * y * (y ^ 2 - x ^ 2) ≤ 1 := by
  have hb := UnitCircleQuarticExtrema.sharp_bounds x y h
  unfold UnitCircleQuarticExtrema.value at hb
  constructor <;> linarith

#print axioms UnitCircleQuarticExtrema.gap_identities
#print axioms UnitCircleQuarticExtrema.homogeneous_bounds
#print axioms UnitCircleQuarticExtrema.sharp_bounds
#print axioms UnitCircleQuarticExtrema.upper_equality
#print axioms UnitCircleQuarticExtrema.lower_equality
#print axioms UnitCircleQuarticExtrema.extremizers
#print axioms UnitCircleQuarticExtrema.maximum
#print axioms UnitCircleQuarticExtrema.minimum
#print axioms solution
