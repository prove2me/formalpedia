-- Prove2me | solution 1 for lean_workbook_plus_74810
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:29:42.560863+00:00
-- url     : https://prove2.me/submissions/0ba2c609-2b2a-4ad0-8b86-040420331f38

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem positive_index_root_bound (n : ℝ) (hn : 1 ≤ n) :
    Real.sqrt n + Real.sqrt (n + 2) > 2 * Real.sqrt (n + 4 / 5) := by
  have hn0 : 0 ≤ n := by linarith
  have ha := Real.sq_sqrt hn0
  have hb := Real.sq_sqrt (by linarith : 0 ≤ n + 2)
  have hc := Real.sq_sqrt (by linarith : 0 ≤ n + 4 / 5)
  have hp0 : 0 ≤ Real.sqrt n * Real.sqrt (n + 2) := by positivity
  have hp2 : (Real.sqrt n * Real.sqrt (n + 2))^2 = n * (n + 2) := by
    rw [mul_pow, ha, hb]
  have hp : n + 3 / 5 < Real.sqrt n * Real.sqrt (n + 2) := by
    by_contra h
    have hle := pow_le_pow_left₀ hp0 (le_of_not_gt h) (n := 2)
    nlinarith only [hn, hp2, hle]
  by_contra h
  have hle := pow_le_pow_left₀ (by positivity :
    0 ≤ Real.sqrt n + Real.sqrt (n + 2)) (le_of_not_gt h) (n := 2)
  nlinarith only [ha, hb, hc, hp, hle]

theorem solution : ¬ (∀ n : ℕ,
    (Real.sqrt n + Real.sqrt (n + 2) : ℝ) > 2 * Real.sqrt (n + 0.8)) := by
  intro h
  have hh := h 0
  norm_num only [Nat.cast_zero, zero_add, Real.sqrt_zero] at hh
  have hs := (sq_lt_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt (4 / 5 : ℝ))
    (Real.sqrt_nonneg (2 : ℝ))).mpr hh
  nlinarith only [hs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

#print axioms positive_index_root_bound
#print axioms solution
