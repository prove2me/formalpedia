-- Prove2me | solution 1 for ForkPinning.cyclicCubic_pins_more_than_S3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:08:13.45236+00:00
-- url     : https://prove2.me/submissions/9ccbd73b-f0dc-44e2-8dfe-61aec4b25c87

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution :
    mutualInfo (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3
      < mutualInfo (id : ZMod 3 → ZMod 3) forkC3 := by
  have hcardP : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
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
  have hHXs : H (signBool : Equiv.Perm (Fin 3) → Bool)
      = negMulLog (1 / 2 : ℝ) + negMulLog (1 / 2 : ℝ) := by
    have e1 : prb (signBool : Equiv.Perm (Fin 3) → Bool) true = 1 / 2 := by
      simp only [prb, cXt, hcardP]; norm_num
    have e2 : prb (signBool : Equiv.Perm (Fin 3) → Bool) false = 1 / 2 := by
      simp only [prb, cXf, hcardP]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHYs : H (forkSplit3 : Equiv.Perm (Fin 3) → Bool)
      = negMulLog (1 / 6 : ℝ) + negMulLog (5 / 6 : ℝ) := by
    have e1 : prb (forkSplit3 : Equiv.Perm (Fin 3) → Bool) true = 1 / 6 := by
      simp only [prb, cYt, hcardP]; norm_num
    have e2 : prb (forkSplit3 : Equiv.Perm (Fin 3) → Bool) false = 5 / 6 := by
      simp only [prb, cYf, hcardP]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHJs : H (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3)
      = negMulLog (1 / 6 : ℝ) + negMulLog (1 / 3 : ℝ) + negMulLog (1 / 2 : ℝ) := by
    have e1 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (true, true)
        = 1 / 6 := by simp only [prb, cJtt, hcardP]; norm_num
    have e2 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (true, false)
        = 1 / 3 := by simp only [prb, cJtf, hcardP]; norm_num
    have e3 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (false, true)
        = 0 := by simp only [prb, cJft, hcardP]; norm_num
    have e4 : prb (joint (signBool : Equiv.Perm (Fin 3) → Bool) forkSplit3) (false, false)
        = 1 / 2 := by simp only [prb, cJff, hcardP]; norm_num
    simp only [H]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool,
      e1, e2, e3, e4, Real.negMulLog_zero, zero_add]
  have hcard3 : Fintype.card (ZMod 3) = 3 := by simp
  -- the identity statistic is uniform on the three classes
  have hfX : ∀ k : ZMod 3, fiber (id : ZMod 3 → ZMod 3) k = {k} := by
    intro k
    ext x
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, id_eq, Finset.mem_singleton]
  have hpX : ∀ k : ZMod 3, prb (id : ZMod 3 → ZMod 3) k = 1 / 3 := by
    intro k
    simp only [prb, hfX k, Finset.card_singleton, hcard3]
    norm_num
  have hHXc : H (id : ZMod 3 → ZMod 3) = 3 * negMulLog (1 / 3 : ℝ) := by
    simp only [H, hpX]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  -- the fork is (1/3, 2/3)
  have hfYt : (fiber forkC3 true).card = 1 := by decide
  have hfYf : (fiber forkC3 false).card = 2 := by decide
  have hpYt : prb forkC3 true = 1 / 3 := by
    simp only [prb, hfYt, hcard3]
    norm_num
  have hpYf : prb forkC3 false = 2 / 3 := by
    simp only [prb, hfYf, hcard3]
    norm_num
  have hHYc : H forkC3 = negMulLog (1 / 3 : ℝ) + negMulLog (2 / 3 : ℝ) := by
    simp only [H]
    rw [Fintype.sum_bool, hpYt, hpYf]
  -- the joint statistic is again uniform on three cells (the fork is a function of the class)
  have hfJ : ∀ (k : ZMod 3) (b : Bool),
      (fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)).card
        = if forkC3 k = b then 1 else 0 := by
    intro k b
    by_cases hb : forkC3 k = b
    · have he : fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b) = {k} := by
        ext x
        simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          id_eq, Finset.mem_singleton]
        constructor
        · intro hx; exact hx.1
        · intro hx; subst hx; exact ⟨rfl, hb⟩
      rw [he, Finset.card_singleton, if_pos hb]
    · have he : fiber (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b) = ∅ := by
        ext x
        simp only [fiber, joint, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq,
          id_eq, Finset.notMem_empty, iff_false, not_and]
        intro hx
        subst hx
        exact hb
      rw [he, Finset.card_empty, if_neg hb]
  have hpJ : ∀ (k : ZMod 3) (b : Bool),
      prb (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)
        = (if forkC3 k = b then (1 : ℝ) else 0) / 3 := by
    intro k b
    simp only [prb, hfJ k b, hcard3]
    by_cases hb : forkC3 k = b
    · simp [hb]
    · simp [hb]
  have hHJc : H (joint (id : ZMod 3 → ZMod 3) forkC3) = 3 * negMulLog (1 / 3 : ℝ) := by
    simp only [H]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ k : ZMod 3,
        (∑ b : Bool, negMulLog (prb (joint (id : ZMod 3 → ZMod 3) forkC3) (k, b)))
          = negMulLog (1 / 3 : ℝ) := by
      intro k
      rw [Fintype.sum_bool, hpJ k true, hpJ k false]
      by_cases hk : forkC3 k = true
      · simp [hk]
      · rw [Bool.not_eq_true] at hk
        simp [hk]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  -- 2^12 = 4096 < 84375 = 3^3 * 5^5
  have hkey : 12 * Real.log 2 < 3 * Real.log 3 + 5 * Real.log 5 := by
    have h1 : Real.log ((2 : ℝ) ^ 12) < Real.log ((3 : ℝ) ^ 3 * (5 : ℝ) ^ 5) := by
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
  have h23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  simp only [mutualInfo, hHXs, hHYs, hHJs, hHXc, hHYc, hHJc, Real.negMulLog_def]
  rw [h12, h13, h16, h56, h23]
  linarith [hkey]
