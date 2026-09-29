-- Prove2me | solution 1 for mme_finite_pair_moment_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T16:35:28.346598+00:00
-- url     : https://prove2.me/submissions/fc78947c-cbc4-4cc8-91c6-f8c69f292e36

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {U T : Type*} [Fintype U] [Nonempty U] [Fintype T]
    (Z : T → U → ℝ) (a : T → ℝ) (m eps : ℝ)
    (hm : 0 < m) (hmn : m ≤ Fintype.card T) (heps : 0 < eps)
    (hZ : ∀ t f, 0 ≤ Z t f ∧ Z t f ≤ 1) (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (hfirst : ∀ t, |(𝔼 f, Z t f) - a t| ≤ 4 / m)
    (hsecond : ∀ t s, t ≠ s → |(𝔼 f, Z t f * Z s f) - a t * a s| ≤ 16 / m) :
    (𝔼 f : U, if eps ≤ |((∑ t, Z t f) - ∑ t, a t) / Fintype.card T| then (1 : ℝ) else 0) ≤
      25 / (m * eps ^ 2) := by
  classical
  let n : ℝ := Fintype.card T
  have hn : 0 < n := hm.trans_le hmn
  let c (t : T) (f : U) := Z t f - a t
  have hdiag (t : T) : (𝔼 f, c t f * c t f) ≤ 1 := by
    apply Finset.expect_le Finset.univ_nonempty
    intro f _
    dsimp [c]
    nlinarith [hZ t f, ha t]
  have hoff (t s : T) (hts : t ≠ s) : (𝔼 f, c t f * c s f) ≤ 24 / m := by
    have hx := abs_le.mp (hfirst t)
    have hy := abs_le.mp (hfirst s)
    have hxy := abs_le.mp (hsecond t s hts)
    have hlowx := mul_le_mul_of_nonneg_left hx.1 (ha s).1
    have hlowy := mul_le_mul_of_nonneg_left hy.1 (ha t).1
    have hax := mul_le_mul_of_nonneg_right (ha s).2 (show (0 : ℝ) ≤ 4 / m by positivity)
    have hay := mul_le_mul_of_nonneg_right (ha t).2 (show (0 : ℝ) ≤ 4 / m by positivity)
    have heq : (𝔼 f, c t f * c s f) =
        (𝔼 f, Z t f * Z s f) - a s * (𝔼 f, Z t f) - a t * (𝔼 f, Z s f) + a t * a s := by
      calc
        _ = (𝔼 f, (Z t f * Z s f - a s * Z t f - a t * Z s f + a t * a s)) := by
          apply Finset.expect_congr rfl; intro f _; dsimp [c]; ring
        _ = _ := by
          simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
            ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
    rw [heq]
    simp only [div_eq_mul_inv] at hlowx hlowy hax hay hxy ⊢
    nlinarith only [hlowx, hlowy, hax, hay, hxy.2]
  have hentry (t s : T) : (𝔼 f, c t f * c s f) ≤ (if t = s then (1 : ℝ) else 0) + 24 / m := by
    by_cases h : t = s
    · subst s; simp only [↓reduceIte]; exact (hdiag t).trans (le_add_of_nonneg_right (by positivity))
    · simpa [h] using hoff t s h
  have hsquare : (𝔼 f, (∑ t, c t f) ^ 2) ≤ n + n ^ 2 * (24 / m) := by
    calc
      _ = ∑ t, ∑ s, (𝔼 f, c t f * c s f) := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.expect_sum_comm]
        exact Finset.sum_comm
      _ ≤ ∑ t : T, ∑ s : T, ((if t = s then (1 : ℝ) else 0) + 24 / m) := by
        exact Finset.sum_le_sum (fun t _ ↦ Finset.sum_le_sum (fun s _ ↦ hentry t s))
      _ = _ := by simp [Finset.sum_add_distrib, n, pow_two]; ring
  have hnormalized : (𝔼 f, ((∑ t, c t f) / n) ^ 2) ≤ 25 / m := by
    have heq : (𝔼 f, ((∑ t, c t f) / n) ^ 2) = (𝔼 f, (∑ t, c t f) ^ 2) / n ^ 2 := by
      simp only [div_pow, ← Finset.expect_div]
    rw [heq]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
    have hmn' : n * m ≤ n ^ 2 := by nlinarith
    have hbound : n + n ^ 2 * (24 / m) ≤ (25 / m) * n ^ 2 := by
      field_simp
      nlinarith
    exact hsquare.trans hbound
  have hmarkov : eps ^ 2 *
      (𝔼 f : U, if eps ≤ |(∑ t, c t f) / n| then (1 : ℝ) else 0) ≤
      (𝔼 f, ((∑ t, c t f) / n) ^ 2) := by
    rw [Finset.mul_expect]
    apply Finset.expect_le_expect
    intro f _
    by_cases h : eps ≤ |(∑ t, c t f) / n|
    · simp only [h, ↓reduceIte, mul_one]
      nlinarith [sq_abs ((∑ t, c t f) / n)]
    · simp only [h, ↓reduceIte, mul_zero]; positivity
  have hresult : (𝔼 f : U, if eps ≤ |(∑ t, c t f) / n| then (1 : ℝ) else 0) ≤
      25 / (m * eps ^ 2) := by
    have h := hmarkov.trans hnormalized
    apply (le_div_iff₀ (mul_pos hm (sq_pos_of_pos heps))).mpr
    have ht := (le_div_iff₀ hm).mp h
    nlinarith
  simpa only [c, n, Finset.sum_sub_distrib] using hresult
