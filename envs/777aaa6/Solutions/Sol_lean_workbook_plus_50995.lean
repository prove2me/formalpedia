-- Prove2me | solution 1 for lean_workbook_plus_50995
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:47:57.36574+00:00
-- url     : https://prove2.me/submissions/d5844834-abc6-4a67-97ec-222e63716d00

import Mathlib

namespace EllipseSquareDifferenceRange

def Constraint (x y : ℝ) : Prop :=
  x * y + (x + y) * (3 - 2 * x - 2 * y) = 1

def value (x y : ℝ) : ℝ := x ^ 2 - y ^ 2

theorem constraint_iff (x y : ℝ) : Constraint x y ↔
    (x - y) ^ 2 + 7 * (x + y) ^ 2 - 12 * (x + y) + 4 = 0 := by
  unfold Constraint
  constructor <;> intro h <;> nlinarith

theorem gap_identity {x y : ℝ} (h : Constraint x y) :
    1 - (value x y) ^ 2 =
      (x + y - 1) ^ 2 * (7 * (x + y) ^ 2 + 2 * (x + y) + 1) := by
  have he := (constraint_iff x y).mp h
  calc
    1 - (value x y) ^ 2 =
        (x + y - 1) ^ 2 * (7 * (x + y) ^ 2 + 2 * (x + y) + 1) -
        (x + y) ^ 2 * ((x - y) ^ 2 + 7 * (x + y) ^ 2 - 12 * (x + y) + 4) := by
      unfold value
      ring
    _ = _ := by rw [he]; ring

theorem gap_factor_pos (s : ℝ) : 0 < 7 * s ^ 2 + 2 * s + 1 := by
  nlinarith [sq_nonneg (7 * s + 1)]

theorem bounds {x y : ℝ} (h : Constraint x y) :
    -1 ≤ value x y ∧ value x y ≤ 1 := by
  have hg := mul_nonneg (sq_nonneg (x + y - 1)) (gap_factor_pos (x + y)).le
  rw [← gap_identity h] at hg
  constructor <;> nlinarith [sq_nonneg (value x y + 1), sq_nonneg (value x y - 1)]

theorem extremal_iff {x y : ℝ} (h : Constraint x y) :
    (value x y) ^ 2 = 1 ↔ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by
  constructor
  · intro hv
    have hg : (x + y - 1) ^ 2 * (7 * (x + y) ^ 2 + 2 * (x + y) + 1) = 0 := by
      rw [← gap_identity h, hv]
      norm_num
    have hs2 := (mul_eq_zero.mp hg).resolve_right (gap_factor_pos (x + y)).ne'
    have hs : x + y = 1 := by nlinarith [sq_nonneg (x + y - 1)]
    have hxy : x * y = 0 := by
      unfold Constraint at h
      rw [hs] at h
      nlinarith
    rcases mul_eq_zero.mp hxy with hx | hy
    · exact Or.inr ⟨hx, by linarith⟩
    · exact Or.inl ⟨by linarith, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> unfold value <;> ring

theorem upper_equality_iff {x y : ℝ} (h : Constraint x y) :
    value x y = 1 ↔ x = 1 ∧ y = 0 := by
  constructor
  · intro hv
    rcases (extremal_iff h).mp (by rw [hv]; norm_num) with he | ⟨rfl, rfl⟩
    · exact he
    · norm_num [value] at hv
  · rintro ⟨rfl, rfl⟩; unfold value; ring

theorem lower_equality_iff {x y : ℝ} (h : Constraint x y) :
    value x y = -1 ↔ x = 0 ∧ y = 1 := by
  constructor
  · intro hv
    rcases (extremal_iff h).mp (by rw [hv]; norm_num) with ⟨rfl, rfl⟩ | he
    · unfold value at hv
      linarith
    · exact he
  · rintro ⟨rfl, rfl⟩; norm_num [value]

noncomputable def branchSum (t : ℝ) : ℝ := (6 + Real.sqrt (8 - 7 * t ^ 2)) / 7

noncomputable def curveValue (t : ℝ) : ℝ := branchSum t * t

theorem family_feasible (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Constraint ((branchSum t + t) / 2) ((branchSum t - t) / 2) := by
  have ht2 : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + 1)
      (by linarith [ht.2] : 0 ≤ 1 - t)]
  have hr := Real.sq_sqrt (show 0 ≤ 8 - 7 * t ^ 2 by linarith)
  apply (constraint_iff _ _).mpr
  unfold branchSum
  nlinarith [hr]

theorem family_value (t : ℝ) :
    value ((branchSum t + t) / 2) ((branchSum t - t) / 2) = curveValue t := by
  unfold value curveValue
  ring

theorem continuous_curve : Continuous curveValue := by
  unfold curveValue branchSum
  fun_prop

theorem curve_endpoints : curveValue (-1) = -1 ∧ curveValue 1 = 1 := by
  constructor
  · change (6 + Real.sqrt (8 - 7 * (-1 : ℝ) ^ 2)) / 7 * (-1) = -1
    rw [show (8 - 7 * (-1 : ℝ) ^ 2) = 1 by ring, Real.sqrt_one]
    ring
  · change (6 + Real.sqrt (8 - 7 * (1 : ℝ) ^ 2)) / 7 * 1 = 1
    rw [show (8 - 7 * (1 : ℝ) ^ 2) = 1 by ring, Real.sqrt_one]
    ring

theorem attains (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ x y : ℝ, Constraint x y ∧ value x y = z := by
  have hz' : z ∈ Set.Icc (curveValue (-1)) (curveValue 1) := by
    simpa only [curve_endpoints.1, curve_endpoints.2] using hz
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    continuous_curve.continuousOn hz'
  exact ⟨(branchSum t + t) / 2, (branchSum t - t) / 2,
    family_feasible t ht, (family_value t).trans he⟩

theorem attained_range : {z : ℝ | ∃ x y : ℝ, Constraint x y ∧ value x y = z} =
    Set.Icc (-1) 1 := by
  ext z
  constructor
  · rintro ⟨x, y, h, rfl⟩
    exact bounds h
  · exact attains z

theorem least_value : IsLeast
    {z : ℝ | ∃ x y : ℝ, Constraint x y ∧ value x y = z} (-1) := by
  rw [attained_range]
  exact ⟨by norm_num, fun _ h => h.1⟩

theorem greatest_value : IsGreatest
    {z : ℝ | ∃ x y : ℝ, Constraint x y ∧ value x y = z} 1 := by
  rw [attained_range]
  exact ⟨by norm_num, fun _ h => h.2⟩

theorem sharp_absolute_bound (k : ℝ) :
    (∀ x y : ℝ, Constraint x y → |value x y| ≤ k) ↔ 1 ≤ k := by
  constructor
  · intro h
    have hp := h 1 0 (by unfold Constraint; ring)
    have hv : value 1 0 = 1 := by unfold value; ring
    rwa [hv, abs_one] at hp
  · intro hk x y h
    exact (abs_le.mpr (bounds h)).trans hk

end EllipseSquareDifferenceRange

theorem solution (x y : ℝ)
    (h : x * y + (x + y) * (3 - 2 * x - 2 * y) = 1) :
    -1 ≤ x ^ 2 - y ^ 2 ∧ x ^ 2 - y ^ 2 ≤ 1 :=
  EllipseSquareDifferenceRange.bounds h

#print axioms EllipseSquareDifferenceRange.Constraint
#print axioms EllipseSquareDifferenceRange.value
#print axioms EllipseSquareDifferenceRange.constraint_iff
#print axioms EllipseSquareDifferenceRange.gap_identity
#print axioms EllipseSquareDifferenceRange.gap_factor_pos
#print axioms EllipseSquareDifferenceRange.bounds
#print axioms EllipseSquareDifferenceRange.extremal_iff
#print axioms EllipseSquareDifferenceRange.upper_equality_iff
#print axioms EllipseSquareDifferenceRange.lower_equality_iff
#print axioms EllipseSquareDifferenceRange.branchSum
#print axioms EllipseSquareDifferenceRange.curveValue
#print axioms EllipseSquareDifferenceRange.family_feasible
#print axioms EllipseSquareDifferenceRange.family_value
#print axioms EllipseSquareDifferenceRange.continuous_curve
#print axioms EllipseSquareDifferenceRange.curve_endpoints
#print axioms EllipseSquareDifferenceRange.attains
#print axioms EllipseSquareDifferenceRange.attained_range
#print axioms EllipseSquareDifferenceRange.least_value
#print axioms EllipseSquareDifferenceRange.greatest_value
#print axioms EllipseSquareDifferenceRange.sharp_absolute_bound
#print axioms solution
