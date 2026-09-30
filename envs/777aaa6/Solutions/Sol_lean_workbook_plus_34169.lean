-- Prove2me | solution 1 for lean_workbook_plus_34169
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:05:39.005079+00:00
-- url     : https://prove2.me/submissions/13cd1360-1312-4f82-a021-d06bdc1fca84

import Mathlib

namespace TernarySexticZeroLocus

def value (x y z : ℝ) : ℝ :=
  x ^ 2 * y ^ 2 * z ^ 2 - x * y ^ 4 * z - x ^ 2 * y ^ 3 * z -
    x ^ 5 * y + y ^ 6 + x ^ 6

def residual (x y : ℝ) : ℝ :=
  3 * (2 * x ^ 2 + x * y) ^ 2 + (3 * x * y + 2 * y ^ 2) ^ 2 + 5 * y ^ 4

theorem gap_identity (x y z : ℝ) :
    12 * value x y z = 3 * (2 * x * y * z - y ^ 2 * (x + y)) ^ 2 +
      (x - y) ^ 2 * residual x y := by
  unfold value residual
  ring

theorem residual_nonneg (x y : ℝ) : 0 ≤ residual x y := by
  unfold residual
  positivity

theorem source_bound (x y z : ℝ) : 0 ≤ value x y z := by
  have h1 : 0 ≤ 3 * (2 * x * y * z - y ^ 2 * (x + y)) ^ 2 := by positivity
  have h2 := mul_nonneg (sq_nonneg (x - y)) (residual_nonneg x y)
  linarith only [gap_identity x y z, h1, h2]

theorem residual_zero_iff (x y : ℝ) : residual x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro he
    have h1 := sq_nonneg (2 * x ^ 2 + x * y)
    have h2 := sq_nonneg (3 * x * y + 2 * y ^ 2)
    have h4 := pow_nonneg (sq_nonneg y) 2
    have hy4 : y ^ 4 = 0 := by unfold residual at he; nlinarith only [he, h1, h2, h4]
    have hy : y = 0 := eq_zero_of_pow_eq_zero hy4
    have hx4 : x ^ 4 = 0 := by
      unfold residual at he
      rw [hy] at he
      nlinarith only [he]
    exact ⟨eq_zero_of_pow_eq_zero hx4, hy⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [residual]

theorem diagonal_identity (x z : ℝ) : value x x z = x ^ 4 * (z - x) ^ 2 := by
  unfold value
  ring

theorem zero_iff (x y z : ℝ) :
    value x y z = 0 ↔ x = y ∧ (x = 0 ∨ z = x) := by
  constructor
  · intro he
    have h1 : 0 ≤ 3 * (2 * x * y * z - y ^ 2 * (x + y)) ^ 2 := by positivity
    have h2 := mul_nonneg (sq_nonneg (x - y)) (residual_nonneg x y)
    have hz : (x - y) ^ 2 * residual x y = 0 := by
      linarith only [gap_identity x y z, he, h1, h2]
    have hxy : x = y := by
      rcases mul_eq_zero.mp hz with hs | hr
      · exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs)
      · obtain ⟨hx, hy⟩ := (residual_zero_iff x y).mp hr
        exact hx.trans hy.symm
    refine ⟨hxy, ?_⟩
    rw [← hxy, diagonal_identity] at he
    rcases mul_eq_zero.mp he with hx | hz
    · exact Or.inl (eq_zero_of_pow_eq_zero hx)
    · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz))
  · rintro ⟨hxy, hx | hz⟩
    · rw [← hxy, hx]
      norm_num [value]
    · rw [← hxy, hz, diagonal_identity]
      simp

theorem strictly_positive_iff (x y z : ℝ) :
    0 < value x y z ↔ ¬ (x = y ∧ (x = 0 ∨ z = x)) := by
  rw [← zero_iff]
  constructor
  · intro h
    exact ne_of_gt h
  · intro h
    exact lt_of_le_of_ne (source_bound x y z) (Ne.symm h)

theorem coordinate_slice (x : ℝ) : value x 0 0 = x ^ 6 := by
  simp [value]

theorem attains {w : ℝ} (hw : 0 ≤ w) : ∃ x y z : ℝ, value x y z = w := by
  refine ⟨w ^ (1 / 6 : ℝ), 0, 0, ?_⟩
  rw [coordinate_slice]
  simpa using Real.rpow_inv_natCast_pow hw (by norm_num : (6 : ℕ) ≠ 0)

theorem attained_range : {w : ℝ | ∃ x y z : ℝ, value x y z = w} = Set.Ici 0 := by
  ext w
  constructor
  · rintro ⟨x, y, z, rfl⟩
    exact source_bound x y z
  · exact attains

theorem least_value : IsLeast {w : ℝ | ∃ x y z : ℝ, value x y z = w} 0 := by
  rw [attained_range]
  exact ⟨by simp, fun _ h => h⟩

theorem sharp_lower_constant (k : ℝ) : (∀ x y z : ℝ, k ≤ value x y z) ↔ k ≤ 0 := by
  constructor
  · intro h
    simpa [value] using h 0 0 0
  · intro hk x y z
    exact hk.trans (source_bound x y z)

end TernarySexticZeroLocus

theorem solution (x y z : ℝ) :
    x ^ 2 * y ^ 2 * z ^ 2 - x * y ^ 4 * z - x ^ 2 * y ^ 3 * z -
      x ^ 5 * y + y ^ 6 + x ^ 6 ≥ 0 :=
  TernarySexticZeroLocus.source_bound x y z

#print axioms TernarySexticZeroLocus.value
#print axioms TernarySexticZeroLocus.residual
#print axioms TernarySexticZeroLocus.gap_identity
#print axioms TernarySexticZeroLocus.residual_nonneg
#print axioms TernarySexticZeroLocus.source_bound
#print axioms TernarySexticZeroLocus.residual_zero_iff
#print axioms TernarySexticZeroLocus.diagonal_identity
#print axioms TernarySexticZeroLocus.zero_iff
#print axioms TernarySexticZeroLocus.strictly_positive_iff
#print axioms TernarySexticZeroLocus.coordinate_slice
#print axioms TernarySexticZeroLocus.attains
#print axioms TernarySexticZeroLocus.attained_range
#print axioms TernarySexticZeroLocus.least_value
#print axioms TernarySexticZeroLocus.sharp_lower_constant
#print axioms solution
