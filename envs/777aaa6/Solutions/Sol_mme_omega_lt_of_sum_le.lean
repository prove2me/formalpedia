-- Prove2me | solution 1 for mme_omega_lt_of_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T20:35:27.165178+00:00
-- url     : https://prove2.me/submissions/e3ff3b56-e536-4d82-aaf8-2fa54edd0bca

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_omega_strassen

open MME Real

universe u

/-- Numerical helper: `211/20 < 16^(17/20)`. -/
private theorem rpow_16_bound : (211 : ℝ) / 20 < (16 : ℝ) ^ ((17 : ℝ) / 20) := by
  have h_eq : (16 : ℝ) ^ ((17 : ℝ) / 20) = ((2 : ℝ) ^ (17 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) from by norm_num,
        ← rpow_natCast (2 : ℝ) 4,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 2),
        show ((4 : ℕ) : ℝ) * ((17 : ℝ) / 20) = ↑(17 : ℕ) * ((1 : ℝ) / 5) from by push_cast; ring,
        rpow_mul (by positivity : (0 : ℝ) ≤ 2), rpow_natCast]
  rw [h_eq, show (211 : ℝ) / 20 = (((211 : ℝ) / 20) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) from by
    rw [← rpow_natCast ((211 : ℝ) / 20) 5,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 211 / 20),
        show ((5 : ℕ) : ℝ) * ((1 : ℝ) / 5) = 1 from by push_cast; ring, rpow_one]]
  exact rpow_lt_rpow (by positivity) (by norm_num) (by positivity)

/-- Numerical helper: `323/50 < 9^(17/20)`. -/
private theorem rpow_9_bound : (323 : ℝ) / 50 < (9 : ℝ) ^ ((17 : ℝ) / 20) := by
  have h_eq : (9 : ℝ) ^ ((17 : ℝ) / 20) = ((3 : ℝ) ^ (17 : ℕ)) ^ ((1 : ℝ) / 10) := by
    rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℕ) from by norm_num,
        ← rpow_natCast (3 : ℝ) 2,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 3),
        show ((2 : ℕ) : ℝ) * ((17 : ℝ) / 20) = ↑(17 : ℕ) * ((1 : ℝ) / 10) from by push_cast; ring,
        rpow_mul (by positivity : (0 : ℝ) ≤ 3), rpow_natCast]
  rw [h_eq, show (323 : ℝ) / 50 = (((323 : ℝ) / 50) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) from by
    rw [← rpow_natCast ((323 : ℝ) / 50) 10,
        ← rpow_mul (by positivity : (0 : ℝ) ≤ 323 / 50),
        show ((10 : ℕ) : ℝ) * ((1 : ℝ) / 10) = 1 from by push_cast; ring, rpow_one]]
  exact rpow_lt_rpow (by positivity) (by norm_num) (by positivity)

/-- The Schönhage inequality `16^(ω/3) + 9^(ω/3) ≤ 17` forces `ω < 51/20`.
Increasing-ness of `rpow` in the exponent plus `16^(17/20) + 9^(17/20) > 17`. -/
theorem solution {K : Type u} [Field K]
    (h : (16 : ℝ) ^ (matMulExp_strassen K / 3) + (9 : ℝ) ^ (matMulExp_strassen K / 3) ≤ 17) :
    matMulExp_strassen K < 51 / 20 := by
  by_contra h_ge
  rw [not_lt] at h_ge
  have h_exp : (17 : ℝ) / 20 ≤ matMulExp_strassen K / 3 := by linarith
  have h16 : (16 : ℝ) ^ ((17 : ℝ) / 20) ≤ (16 : ℝ) ^ (matMulExp_strassen K / 3) :=
    rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) h_exp
  have h9 : (9 : ℝ) ^ ((17 : ℝ) / 20) ≤ (9 : ℝ) ^ (matMulExp_strassen K / 3) :=
    rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) h_exp
  linarith [rpow_16_bound, rpow_9_bound]
