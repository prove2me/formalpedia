-- Prove2me | solution 1 for ForkPinning.semiprime_OR_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:03:50.809977+00:00
-- url     : https://prove2.me/submissions/08709a71-9b8c-4498-96ef-68632191d6b7

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningGalois
import Definitions.Def_Probability_ForkPinningSemiprime
open ForkPinning Finset Real in
theorem solution :
    mutualInfo cubicClassOfN splitOR
      = Real.log 3 - (5 / 9) * Real.log 5 - (2 / 9) * Real.log 2 := by
  have hcard3 : Fintype.card (ZMod 3) = 3 := by simp
  have hcard9 : Fintype.card (ZMod 3 × ZMod 3) = 9 := by simp
  -- ===== side A: the semiprime class against "some factor splits" =====
  have cA : ∀ g : ZMod 3, (fiber cubicClassOfN g).card = 3 := by decide
  have cYt : (fiber splitOR true).card = 5 := by decide
  have cYf : (fiber splitOR false).card = 4 := by decide
  have hpair : ∀ g : ZMod 3,
      ((fiber (joint cubicClassOfN splitOR) (g, true)).card = 1
        ∧ (fiber (joint cubicClassOfN splitOR) (g, false)).card = 2)
      ∨ ((fiber (joint cubicClassOfN splitOR) (g, true)).card = 2
        ∧ (fiber (joint cubicClassOfN splitOR) (g, false)).card = 1) := by decide
  have hHXa : H cubicClassOfN = 3 * negMulLog (1 / 3 : ℝ) := by
    have e : ∀ g : ZMod 3, prb cubicClassOfN g = 1 / 3 := by
      intro g
      simp only [prb, cA g, hcard9]
      norm_num
    simp only [H, e]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hHYa : H splitOR = negMulLog (5 / 9 : ℝ) + negMulLog (4 / 9 : ℝ) := by
    have e1 : prb splitOR true = 5 / 9 := by simp only [prb, cYt, hcard9]; norm_num
    have e2 : prb splitOR false = 4 / 9 := by simp only [prb, cYf, hcard9]; norm_num
    simp only [H]
    rw [Fintype.sum_bool, e1, e2]
  have hHJa : H (joint cubicClassOfN splitOR)
      = 3 * (negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ)) := by
    have hinner : ∀ g : ZMod 3,
        (∑ b : Bool, negMulLog (prb (joint cubicClassOfN splitOR) (g, b)))
          = negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ) := by
      intro g
      rw [Fintype.sum_bool]
      rcases hpair g with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have q1 : prb (joint cubicClassOfN splitOR) (g, true) = 1 / 9 := by
          simp only [prb, h1, hcard9]; norm_num
        have q2 : prb (joint cubicClassOfN splitOR) (g, false) = 2 / 9 := by
          simp only [prb, h2, hcard9]; norm_num
        rw [q1, q2]
      · have q1 : prb (joint cubicClassOfN splitOR) (g, true) = 2 / 9 := by
          simp only [prb, h1, hcard9]; norm_num
        have q2 : prb (joint cubicClassOfN splitOR) (g, false) = 1 / 9 := by
          simp only [prb, h2, hcard9]; norm_num
        rw [q1, q2]
        ring
    simp only [H]
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [Finset.sum_const, Finset.card_univ, hcard3, nsmul_eq_mul]
    norm_num
  have hA : mutualInfo cubicClassOfN splitOR
      = 3 * negMulLog (1 / 3 : ℝ) + (negMulLog (5 / 9 : ℝ) + negMulLog (4 / 9 : ℝ))
        - 3 * (negMulLog (1 / 9 : ℝ) + negMulLog (2 / 9 : ℝ)) := by
    simp only [mutualInfo, hHXa, hHYa, hHJa]
  have hL9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have hl19 : Real.log (1 / 9 : ℝ) = -(2 * Real.log 3) := by
    rw [one_div, Real.log_inv, hL9]
  have hl29 : Real.log (2 / 9 : ℝ) = Real.log 2 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9]
  have hl59 : Real.log (5 / 9 : ℝ) = Real.log 5 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9]
  have hl49 : Real.log (4 / 9 : ℝ) = 2 * Real.log 2 - 2 * Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), hL9, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  rw [hA]
  simp only [Real.negMulLog_def]
  rw [hl13, hl59, hl49, hl19, hl29]
  ring
