-- Prove2me | solution 3 for BookSixth.crossing_lemma
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-22T21:21:09.25399+00:00
-- url     : https://prove2.me/submissions/b42df2e6-5a14-4a2c-936e-d61147c9db9a

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_drawing_sampling_bound

set_option autoImplicit false

open scoped BigOperators
open BookSixth

/- Crossing lemma (Aigner–Ziegler, *Proofs from THE BOOK*, 6th ed., Chapter 45,
    Theorem 4), punch-line step: from the vertex-sampling inequality
    `p^2 * M ≤ 3*p*N + p^4 * crossings` (proved in `drawing_sampling_bound`)
    choose p := 4N/M — which is ≤ 1 precisely because 4N ≤ M — and clear
    denominators to obtain M^3 ≤ 64 * N^2 * crossings. -/

theorem solution {N M : ℕ} (hN : 0 < N) (hM : 4*N ≤ M) (D : PlaneDrawing N M) :
    M^3 ≤ 64 * N^2 * D.crossings.card := by
  have hN0 : (0:ℝ) < (N:ℝ) := by positivity
  have h4NM : (4*(N:ℝ)) ≤ (M:ℝ) := by exact_mod_cast hM
  have hM0 : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le (by positivity) h4NM
  set p : ℝ := 4*(N:ℝ)/(M:ℝ) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def]
    exact (div_le_one hM0).mpr h4NM
  have hpM : p * (M:ℝ) = 4 * (N:ℝ) := by rw [hp_def]; field_simp
  have h := drawing_sampling_bound D p (le_of_lt hp_pos) hp1
  have hp2 : p^2 * (M:ℝ) = 4 * p * (N:ℝ) := by
    rw [show p^2 * (M:ℝ) = p * (p * (M:ℝ)) from by ring, hpM]; ring
  rw [hp2] at h
  -- h : 4 * p * N ≤ 3 * p * N + p^4 * C
  have h1 : p * (N:ℝ) ≤ p^4 * (D.crossings.card : ℝ) := by linarith
  have h2 : (N:ℝ) ≤ p^3 * (D.crossings.card : ℝ) := by
    have hg : p * (N:ℝ) ≤ p * (p^3 * (D.crossings.card:ℝ)) := by
      rw [show p * (p^3 * (D.crossings.card:ℝ)) = p^4 * (D.crossings.card:ℝ) from by ring]
      exact h1
    exact (mul_le_mul_iff_right₀ hp_pos).mp hg
  have hM4 : (M:ℝ) = 4 * (N:ℝ) / p := by
    rw [hp_def]; field_simp
  have key : (M:ℝ)^3 ≤ 64 * (N:ℝ)^2 * (D.crossings.card:ℝ) := by
    rw [hM4, show (4 * (N:ℝ) / p)^3 = 64 * (N:ℝ)^3 / p^3 from by field_simp; ring,
      div_le_iff₀ (pow_pos hp_pos 3),
      show 64 * (N:ℝ)^3 = 64 * (N:ℝ)^2 * (N:ℝ) from by ring,
      show 64 * (N:ℝ)^2 * (D.crossings.card:ℝ) * p^3
        = 64 * (N:ℝ)^2 * (p^3 * (D.crossings.card:ℝ)) from by ring]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact_mod_cast key
