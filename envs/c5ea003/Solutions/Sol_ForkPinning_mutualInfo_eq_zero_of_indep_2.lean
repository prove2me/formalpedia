-- Prove2me | solution 2 for ForkPinning.mutualInfo_eq_zero_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:00:39.238166+00:00
-- url     : https://prove2.me/submissions/d3804c5c-8ee4-4587-b870-1e74106afc8e

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (X : Ω → κ) (Y : Ω → β)
    (h : ∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b) : mutualInfo X Y = 0 := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsumX : ∑ k : κ, prb X k = 1 := by
    simp only [prb, fiber]
    rw [← Finset.sum_div, div_eq_one_iff_eq hΩ, ← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ (α := Ω)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hsumY : ∑ b : β, prb Y b = 1 := by
    simp only [prb, fiber]
    rw [← Finset.sum_div, div_eq_one_iff_eq hΩ, ← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ (α := Ω)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hinner : ∀ k : κ, (∑ b : β, negMulLog (prb (joint X Y) (k, b)))
      = negMulLog (prb X k) + prb X k * (∑ b : β, negMulLog (prb Y b)) := by
    intro k
    have hstep : ∀ b : β, negMulLog (prb (joint X Y) (k, b))
        = prb Y b * negMulLog (prb X k) + prb X k * negMulLog (prb Y b) := by
      intro b
      rw [h k b]
      exact Real.negMulLog_mul _ _
    simp only [hstep]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsumY, one_mul]
  have hHJ : H (joint X Y) = H X + H Y := by
    simp only [H]
    rw [Fintype.sum_prod_type]
    simp only [hinner]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumX, one_mul]
  simp only [mutualInfo, hHJ]
  ring
