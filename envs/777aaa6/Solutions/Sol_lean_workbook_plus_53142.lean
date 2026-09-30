-- Prove2me | solution 1 for lean_workbook_plus_53142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:54.593861+00:00
-- url     : https://prove2.me/submissions/aa2b7336-8b5f-444d-9190-793be331a793

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem quadratic_coefficient_evaluation_identity (a b c r : ℝ) (hr : 0 < r) :
    a / (r + 2) + b / (r + 1) + c / r =
      (r + 2) / (r + 1) ^ 2 *
        (a * ((r + 1) / (r + 2)) ^ 2 + b * ((r + 1) / (r + 2)) + c) +
      c / (r * (r + 1) ^ 2) := by
  have h0 := ne_of_gt hr
  have h1 : r + 1 ≠ 0 := by positivity
  have h2 : r + 2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem nonnegative_quadratic_two_zeros (a b c t : ℝ)
    (hq : ∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 2 + b * x + c)
    (ht : 0 < t) (hc : c = 0) (hroot : a * t ^ 2 + b * t + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hhalf := hq (t / 2) (by positivity)
  have hdouble := hq (2 * t) (by positivity)
  have hat : a * t ^ 2 = 0 := by nlinarith
  have ha : a = 0 := (mul_eq_zero.mp hat).resolve_right (by positivity)
  have hbt : b * t = 0 := by nlinarith
  exact ⟨ha, (mul_eq_zero.mp hbt).resolve_right (ne_of_gt ht), hc⟩

theorem positive_quadratic_weighted_coefficients (a b c r : ℝ)
    (hq : ∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 2 + b * x + c) (hr : 0 < r) :
    0 ≤ a / (r + 2) + b / (r + 1) + c / r := by
  rw [quadratic_coefficient_evaluation_identity a b c r hr]
  have hc : 0 ≤ c := by simpa using hq 0 (by norm_num)
  have ht := hq ((r + 1) / (r + 2)) (by positivity)
  exact add_nonneg (mul_nonneg (by positivity) ht) (div_nonneg hc (by positivity))

theorem positive_quadratic_weighted_equality (a b c r : ℝ)
    (hq : ∀ x : ℝ, 0 ≤ x → 0 ≤ a * x ^ 2 + b * x + c) (hr : 0 < r) :
    a / (r + 2) + b / (r + 1) + c / r = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [quadratic_coefficient_evaluation_identity a b c r hr] at h
    have hc : 0 ≤ c := by simpa using hq 0 (by norm_num)
    have ht := hq ((r + 1) / (r + 2)) (by positivity)
    have hw : 0 < (r + 2) / (r + 1) ^ 2 := by positivity
    have hd : 0 < r * (r + 1) ^ 2 := by positivity
    have hn1 := mul_nonneg hw.le ht
    have hn2 := div_nonneg hc hd.le
    have hz1 : (r + 2) / (r + 1) ^ 2 *
        (a * ((r + 1) / (r + 2)) ^ 2 + b * ((r + 1) / (r + 2)) + c) = 0 := by
      linarith
    have hz2 : c / (r * (r + 1) ^ 2) = 0 := by linarith
    have hc0 : c = 0 := (div_eq_zero_iff.mp hz2).resolve_right (ne_of_gt hd)
    have hroot : a * ((r + 1) / (r + 2)) ^ 2 + b * ((r + 1) / (r + 2)) + c = 0 :=
      (mul_eq_zero.mp hz1).resolve_left (ne_of_gt hw)
    exact nonnegative_quadratic_two_zeros a b c ((r + 1) / (r + 2)) hq
      (by positivity) hc0 hroot
  · rintro ⟨rfl, rfl, rfl⟩
    simp

theorem solution (a b c : ℝ)
    (ha : ∀ x : ℝ, x ≥ 0 → a * x ^ 2 + b * x + c ≥ 0) :
    a / 2008 + b / 2007 + c / 2006 ≥ 0 := by
  have h := positive_quadratic_weighted_coefficients a b c 2006 ha (by norm_num)
  norm_num at h
  exact h

#print axioms solution
#print axioms positive_quadratic_weighted_coefficients
#print axioms positive_quadratic_weighted_equality
