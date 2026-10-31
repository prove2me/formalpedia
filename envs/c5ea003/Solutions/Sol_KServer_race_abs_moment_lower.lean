-- Prove2me | solution 1 for KServer.race_abs_moment_lower
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T16:41:46.834012+00:00
-- url     : https://prove2.me/submissions/50dc12de-8f2a-4fa1-bece-e2c13670049a

import Mathlib

set_option autoImplicit false

open scoped BigOperators

theorem solution {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (Z : Ω → ℝ)
    (hP : ∀ ω, 0 ≤ P ω) (s : ℝ) (hs : 0 < s)
    (hsecond : s ^ 2 / 4 ≤ ∑ ω, P ω * Z ω ^ 2)
    (hfourth : (∑ ω, P ω * Z ω ^ 4) ≤ 4 * s ^ 4) :
    s / 50 ≤ ∑ ω, P ω * |Z ω| := by
  have hpoint (z : ℝ) : 64 * s ^ 2 * z ^ 2 ≤ 512 * s ^ 3 * |z| + z ^ 4 := by
    have hz : |z| ^ 2 = z ^ 2 := sq_abs z
    have hza := abs_nonneg z
    by_cases h : |z| ≤ 8 * s
    · have h1 := mul_le_mul_of_nonneg_left h hza
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 64 * s ^ 2 by positivity)
      nlinarith [sq_nonneg (z ^ 2)]
    · have h1 : 64 * s ^ 2 ≤ z ^ 2 := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg z)
      have h3 : 0 ≤ 512 * s ^ 3 * |z| := by positivity
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left (hpoint (Z ω)) (hP ω))
  have heq1 : (∑ ω, P ω * (64 * s ^ 2 * Z ω ^ 2)) =
      64 * s ^ 2 * ∑ ω, P ω * Z ω ^ 2 := by rw [Finset.mul_sum]; congr 1; funext ω; ring
  have heq2 : (∑ ω, P ω * (512 * s ^ 3 * |Z ω| + Z ω ^ 4)) =
      512 * s ^ 3 * (∑ ω, P ω * |Z ω|) + ∑ ω, P ω * Z ω ^ 4 := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [heq1, heq2] at hsum
  have h2 := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 64 * s ^ 2 by positivity)
  by_contra hn
  have hn' : (∑ ω, P ω * |Z ω|) < s / 50 := lt_of_not_ge hn
  have hlt := mul_lt_mul_of_pos_left hn' (show 0 < 512 * s ^ 3 by positivity)
  have hpos : 0 < s ^ 4 := by positivity
  nlinarith
