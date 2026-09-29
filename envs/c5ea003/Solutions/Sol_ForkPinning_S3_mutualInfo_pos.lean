-- Prove2me | solution 1 for ForkPinning.S3_mutualInfo_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:48:17.07877+00:00
-- url     : https://prove2.me/submissions/810e3a86-1fba-4e09-a1a7-413c3732f29b

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution : 0 < mutualInfo (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3 := by
  have hcard : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    rfl
  -- fibre counts in S₃ (3 even, 3 odd; only the identity is "unsplit")
  have cXt : (fiber (signBool : Equiv.Perm (Fin 3) → Bool) true).card = 3 := by decide
  have cXf : (fiber (signBool : Equiv.Perm (Fin 3) → Bool) false).card = 3 := by decide
  have cYt : (fiber (forkSplit3 : Equiv.Perm (Fin 3) → Bool) true).card = 1 := by decide
  have cYf : (fiber (forkSplit3 : Equiv.Perm (Fin 3) → Bool) false).card = 5 := by decide
  have cJtt : (fiber (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      (true, true)).card = 1 := by decide
  have cJtf : (fiber (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      (true, false)).card = 2 := by decide
  have cJft : (fiber (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      (false, true)).card = 0 := by decide
  have cJff : (fiber (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      (false, false)).card = 3 := by decide
  have hHX : H (signBool : Equiv.Perm (Fin 3) → Bool)
      = negMulLog (1 / 2 : ℝ) + negMulLog (1 / 2 : ℝ) := by
    have e1 : prb (signBool : Equiv.Perm (Fin 3) → Bool) true = 1 / 2 := by
      simp only [prb, cXt, hcard]; norm_num
    have e2 : prb (signBool : Equiv.Perm (Fin 3) → Bool) false = 1 / 2 := by
      simp only [prb, cXf, hcard]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHY : H (forkSplit3 : Equiv.Perm (Fin 3) → Bool)
      = negMulLog (1 / 6 : ℝ) + negMulLog (5 / 6 : ℝ) := by
    have e1 : prb (forkSplit3 : Equiv.Perm (Fin 3) → Bool) true = 1 / 6 := by
      simp only [prb, cYt, hcard]; norm_num
    have e2 : prb (forkSplit3 : Equiv.Perm (Fin 3) → Bool) false = 5 / 6 := by
      simp only [prb, cYf, hcard]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHJ : H (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      = negMulLog (1 / 6 : ℝ) + negMulLog (1 / 3 : ℝ) + negMulLog (1 / 2 : ℝ) := by
    have e1 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (true, true)
        = 1 / 6 := by simp only [prb, cJtt, hcard]; norm_num
    have e2 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (true, false)
        = 1 / 3 := by simp only [prb, cJtf, hcard]; norm_num
    have e3 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (false, true)
        = 0 := by simp only [prb, cJft, hcard]; norm_num
    have e4 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (false, false)
        = 1 / 2 := by simp only [prb, cJff, hcard]; norm_num
    simp only [H]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
      e1, e2, e3, e4, Real.negMulLog_zero, zero_add]
  -- 2^8 · 3^3 = 6912 > 3125 = 5^5
  have hkey : 5 * Real.log 5 < 8 * Real.log 2 + 3 * Real.log 3 := by
    have h1 : Real.log ((5 : ℝ) ^ 5) < Real.log ((2 : ℝ) ^ 8 * (3 : ℝ) ^ 3) := by
      apply Real.log_lt_log (by positivity)
      norm_num
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have h13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have h16 : Real.log (1 / 6 : ℝ) = -(Real.log 2 + Real.log 3) := by
    rw [one_div, Real.log_inv, hL6]
  have h56 : Real.log (5 / 6 : ℝ) = Real.log 5 - (Real.log 2 + Real.log 3) := by
    rw [Real.log_div (by norm_num) (by norm_num), hL6]
  simp only [mutualInfo, hHX, hHY, hHJ, Real.negMulLog_def]
  rw [h12, h13, h16, h56]
  linarith [hkey]
