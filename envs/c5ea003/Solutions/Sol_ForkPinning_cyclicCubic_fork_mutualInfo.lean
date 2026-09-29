-- Prove2me | solution 1 for ForkPinning.cyclicCubic_fork_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:43:15.981708+00:00
-- url     : https://prove2.me/submissions/2c5b3c23-5885-453f-a48d-b7d520ddbf18

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
open ForkPinning Finset Real in
theorem solution :
    mutualInfo (id : ZMod 3 → ZMod 3) forkC3 = Real.log 3 - (2 / 3) * Real.log 2 := by
  have hcard : Fintype.card (ZMod 3) = 3 := by simp
  -- the identity statistic is uniform on the three classes
  have hfX : ∀ k : ZMod 3, fiber (id : ZMod 3 → ZMod 3) k = {k} := by
    intro k
    ext x
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, id_eq, Finset.mem_singleton]
  have hpX : ∀ k : ZMod 3, prb (id : ZMod 3 → ZMod 3) k = 1 / 3 := by
    intro k
    simp only [prb, hfX k, Finset.card_singleton, hcard]
    norm_num
  have hHX : H (id : ZMod 3 → ZMod 3) = 3 * negMulLog (1 / 3 : ℝ) := by
    simp only [H, hpX]
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    norm_num
  -- the fork is (1/3, 2/3)
  have hfYt : (fiber forkC3 true).card = 1 := by decide
  have hfYf : (fiber forkC3 false).card = 2 := by decide
  have hpYt : prb forkC3 true = 1 / 3 := by
    simp only [prb, hfYt, hcard]
    norm_num
  have hpYf : prb forkC3 false = 2 / 3 := by
    simp only [prb, hfYf, hcard]
    norm_num
  have hHY : H forkC3 = negMulLog (1 / 3 : ℝ) + negMulLog (2 / 3 : ℝ) := by
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
    simp only [prb, hfJ k b, hcard]
    by_cases hb : forkC3 k = b
    · simp [hb]
    · simp [hb]
  have hHJ : H (joint (id : ZMod 3 → ZMod 3) forkC3) = 3 * negMulLog (1 / 3 : ℝ) := by
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
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    norm_num
  have hl3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hl23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  simp only [mutualInfo, hHX, hHY, hHJ, Real.negMulLog_def]
  rw [hl3, hl23]
  ring
