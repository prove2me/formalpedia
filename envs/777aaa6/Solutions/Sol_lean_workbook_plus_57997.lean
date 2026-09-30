-- Prove2me | solution 1 for lean_workbook_plus_57997
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:27:42.442643+00:00
-- url     : https://prove2.me/submissions/fd7665a7-e31e-4f6d-b0b6-fa9c1e55d062

import Mathlib

namespace OcticUniqueMinimum

def value (x : ℝ) : ℝ := x ^ 8 - x ^ 5 + x ^ 2 - 5 * x + 4

def factor (x : ℝ) : ℝ :=
  x ^ 6 + 2 * x ^ 5 + 3 * x ^ 4 + 3 * x ^ 3 + 3 * x ^ 2 + 3 * x + 4

theorem factorization (x : ℝ) : value x = (x - 1) ^ 2 * factor x := by
  unfold value factor
  ring

theorem square_certificate (x : ℝ) :
    factor x = x ^ 4 * (x + 1) ^ 2 + 2 * x ^ 2 * (x + 3 / 4) ^ 2 +
      (15 / 8) * (x + 4 / 5) ^ 2 + 14 / 5 := by
  unfold factor
  ring

theorem factor_lower_bound (x : ℝ) : 14 / 5 ≤ factor x := by
  rw [square_certificate]
  have h1 : 0 ≤ x ^ 4 * (x + 1) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
  have h2 : 0 ≤ 2 * x ^ 2 * (x + 3 / 4) ^ 2 := by positivity
  linarith only [h1, h2, mul_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 8)
    (sq_nonneg (x + 4 / 5))]

theorem factor_pos (x : ℝ) : 0 < factor x := by
  linarith only [factor_lower_bound x]

theorem quadratic_lower_bound (x : ℝ) : (14 / 5) * (x - 1) ^ 2 ≤ value x := by
  rw [factorization]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (factor_lower_bound x) (sq_nonneg (x - 1))

theorem nonnegative (x : ℝ) : 0 ≤ value x := by
  rw [factorization]
  exact mul_nonneg (sq_nonneg _) (factor_pos x).le

theorem zero_iff (x : ℝ) : value x = 0 ↔ x = 1 := by
  rw [factorization, mul_eq_zero]
  constructor
  · rintro (h | h)
    · nlinarith only [h]
    · exact ((ne_of_gt (factor_pos x)) h).elim
  · rintro rfl
    exact Or.inl (by norm_num)

theorem positive_iff (x : ℝ) : 0 < value x ↔ x ≠ 1 := by
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hn⟩ he
    exact hn ((zero_iff x).mpr he).symm
  · intro hn
    exact ⟨nonnegative x, fun he => hn ((zero_iff x).mp he.symm)⟩

theorem value_continuous : Continuous value := by
  unfold value
  fun_prop

theorem attains {y : ℝ} (hy : 0 ≤ y) : ∃ x : ℝ, 1 ≤ x ∧ value x = y := by
  have h1 : value 1 = 0 := (zero_iff 1).mpr rfl
  have he : y ≤ value (y + 2) := by
    have h := quadratic_lower_bound (y + 2)
    nlinarith only [h, hy, sq_nonneg y]
  have hy' : y ∈ Set.Icc (value 1) (value (y + 2)) := by
    rw [h1]
    exact ⟨hy, he⟩
  obtain ⟨x, hx, hv⟩ := intermediate_value_Icc (by linarith : (1 : ℝ) ≤ y + 2)
    value_continuous.continuousOn hy'
  exact ⟨x, hx.1, hv⟩

theorem attained_range : Set.range value = Set.Ici 0 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact nonnegative x
  · intro hy
    obtain ⟨x, _, hx⟩ := attains hy
    exact ⟨x, hx⟩

theorem least_value : IsLeast (Set.range value) 0 := by
  rw [attained_range]
  exact ⟨by simp, fun _ h => h⟩

theorem additive_nonnegative_iff (c : ℝ) :
    (∀ x : ℝ, x ^ 8 - x ^ 5 + x ^ 2 - 5 * x + c ≥ 0) ↔ 4 ≤ c := by
  constructor
  · intro h
    have := h 1
    norm_num at this
    linarith
  · intro hc x
    have h := nonnegative x
    unfold value at h
    linarith

theorem additive_positive_iff (c : ℝ) :
    (∀ x : ℝ, 0 < x ^ 8 - x ^ 5 + x ^ 2 - 5 * x + c) ↔ 4 < c := by
  constructor
  · intro h
    have := h 1
    norm_num at this
    linarith
  · intro hc x
    have h := nonnegative x
    unfold value at h
    linarith

end OcticUniqueMinimum

theorem solution (x : ℝ) : x ^ 8 - x ^ 5 + x ^ 2 - 5 * x + 4 ≥ 0 :=
  OcticUniqueMinimum.nonnegative x

#print axioms OcticUniqueMinimum.value
#print axioms OcticUniqueMinimum.factor
#print axioms OcticUniqueMinimum.factorization
#print axioms OcticUniqueMinimum.square_certificate
#print axioms OcticUniqueMinimum.factor_lower_bound
#print axioms OcticUniqueMinimum.factor_pos
#print axioms OcticUniqueMinimum.quadratic_lower_bound
#print axioms OcticUniqueMinimum.nonnegative
#print axioms OcticUniqueMinimum.zero_iff
#print axioms OcticUniqueMinimum.positive_iff
#print axioms OcticUniqueMinimum.value_continuous
#print axioms OcticUniqueMinimum.attains
#print axioms OcticUniqueMinimum.attained_range
#print axioms OcticUniqueMinimum.least_value
#print axioms OcticUniqueMinimum.additive_nonnegative_iff
#print axioms OcticUniqueMinimum.additive_positive_iff
#print axioms solution
