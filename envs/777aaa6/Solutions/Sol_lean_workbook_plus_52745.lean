-- Prove2me | solution 1 for lean_workbook_plus_52745
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:00:19.473487+00:00
-- url     : https://prove2.me/submissions/07830da9-26dc-4bd4-b2d9-a83a5bcf9b42

import Mathlib

set_option autoImplicit false

namespace EvenDegreeQuadraticPositivity

theorem gap_identity (n : ℕ) (x : ℝ) :
    (x ^ (2 * n) + 1) * (x ^ 2 - x) + 1 / 2 =
      (1 - x ^ (2 * n)) * (x - x ^ 2) + 2 * (x - 1 / 2) ^ 2 := by
  ring

theorem outside_nonnegative (n : ℕ) (x : ℝ) (hx : x ≤ 0 ∨ 1 ≤ x) :
    0 ≤ (x ^ (2 * n) + 1) * (x ^ 2 - x) := by
  have hp : 0 ≤ x ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul]
    positivity
  have hq : 0 ≤ x ^ 2 - x := by
    rcases hx with hx | hx
    · nlinarith only [sq_nonneg x, hx]
    · nlinarith only [mul_nonneg (show 0 ≤ x by linarith only [hx]) (sub_nonneg.mpr hx)]
  exact mul_nonneg (by linarith only [hp]) hq

theorem lower_bound (n : ℕ) (x : ℝ) :
    -(1 / 2 : ℝ) ≤ (x ^ (2 * n) + 1) * (x ^ 2 - x) := by
  by_cases hx : x ≤ 0
  · have := outside_nonnegative n x (Or.inl hx)
    linarith
  by_cases hx1 : 1 ≤ x
  · have := outside_nonnegative n x (Or.inr hx1)
    linarith
  have h0 : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
  have h1 : x ≤ 1 := le_of_lt (lt_of_not_ge hx1)
  have hp : x ^ (2 * n) ≤ 1 := pow_le_one₀ h0 h1
  have hq : 0 ≤ x - x ^ 2 := by
    nlinarith only [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hg := gap_identity n x
  nlinarith only [hg, mul_nonneg (sub_nonneg.mpr hp) hq, sq_nonneg (x - 1 / 2)]

theorem lower_bound_eq_iff (n : ℕ) (x : ℝ) :
    (x ^ (2 * n) + 1) * (x ^ 2 - x) = -(1 / 2 : ℝ) ↔
      n = 0 ∧ x = 1 / 2 := by
  constructor
  · intro he
    have h0 : 0 < x := by
      by_contra h
      have := outside_nonnegative n x (Or.inl (le_of_not_gt h))
      linarith
    have h1 : x < 1 := by
      by_contra h
      have := outside_nonnegative n x (Or.inr (le_of_not_gt h))
      linarith
    have hp : x ^ (2 * n) ≤ 1 := pow_le_one₀ h0.le h1.le
    have hq : 0 ≤ x - x ^ 2 := by
      nlinarith only [mul_nonneg h0.le (sub_nonneg.mpr h1.le)]
    have hg := gap_identity n x
    have hs : (x - 1 / 2) ^ 2 = 0 := by
      nlinarith only [hg, he, mul_nonneg (sub_nonneg.mpr hp) hq,
        sq_nonneg (x - 1 / 2)]
    have hx : x = 1 / 2 := by nlinarith only [hs]
    refine ⟨?_, hx⟩
    by_contra hn
    have hp' : x ^ (2 * n) < 1 := pow_lt_one₀ h0.le h1 (by omega)
    rw [hx] at hp' he
    nlinarith only [hp', he]
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem strict_lower_bound (n : ℕ) (hn : 0 < n) (x : ℝ) :
    -(1 / 2 : ℝ) < (x ^ (2 * n) + 1) * (x ^ 2 - x) := by
  have hb := lower_bound n x
  by_contra h
  have he : (x ^ (2 * n) + 1) * (x ^ 2 - x) = -(1 / 2 : ℝ) := by linarith
  have := ((lower_bound_eq_iff n x).mp he).1
  omega

theorem uniform_lower_bound_iff (b : ℝ) :
    (∀ n : ℕ, ∀ x : ℝ, b ≤ (x ^ (2 * n) + 1) * (x ^ 2 - x)) ↔ b ≤ -1 / 2 := by
  constructor
  · intro h
    have := h 0 (1 / 2)
    norm_num at this ⊢
    exact this
  · intro hb n x
    have := lower_bound n x
    linarith

theorem uniform_nonnegative_iff (c : ℝ) :
    (∀ n : ℕ, ∀ x : ℝ, 0 ≤ (x ^ (2 * n) + 1) * (x ^ 2 - x) + c) ↔ 1 / 2 ≤ c := by
  constructor
  · intro h
    have := h 0 (1 / 2)
    norm_num at this
    linarith
  · intro hc n x
    have := lower_bound n x
    linarith

theorem uniform_positive_iff (c : ℝ) :
    (∀ n : ℕ, ∀ x : ℝ, 0 < (x ^ (2 * n) + 1) * (x ^ 2 - x) + c) ↔ 1 / 2 < c := by
  constructor
  · intro h
    have := h 0 (1 / 2)
    norm_num at this
    linarith
  · intro hc n x
    have := lower_bound n x
    linarith

theorem threshold_zero_iff (n : ℕ) (x : ℝ) :
    (x ^ (2 * n) + 1) * (x ^ 2 - x) + 1 / 2 = 0 ↔ n = 0 ∧ x = 1 / 2 := by
  rw [← lower_bound_eq_iff]
  constructor <;> intro h <;> linarith

theorem positive_degree_positive (n : ℕ) (hn : 0 < n) (c x : ℝ) (hc : 1 / 2 ≤ c) :
    0 < (x ^ (2 * n) + 1) * (x ^ 2 - x) + c := by
  have := strict_lower_bound n hn x
  linarith

theorem source_lower_bound (x : ℝ) :
    29 / 2 < x ^ 8 - x ^ 7 + x ^ 2 - x + 15 := by
  have h := strict_lower_bound 3 (by omega) x
  norm_num at h
  nlinarith only [h]

theorem source_no_roots : ¬ ∃ x : ℝ, x ^ 8 - x ^ 7 + x ^ 2 - x + 15 = 0 := by
  rintro ⟨x, hx⟩
  have := source_lower_bound x
  linarith

end EvenDegreeQuadraticPositivity

theorem solution : ¬ ∃ x : ℝ, x ^ 8 - x ^ 7 + x ^ 2 - x + 15 = 0 :=
  EvenDegreeQuadraticPositivity.source_no_roots
