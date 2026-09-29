-- Prove2me | solution 1 for ForkPinning.entropy_bool_eq_log_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:29:36.364985+00:00
-- url     : https://prove2.me/submissions/bd4337a8-d3b9-45a2-bfc6-acd928dd276b

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Y : Ω → Bool) :
    H Y = Real.log 2 ↔ prb Y true = 1 / 2 := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    have := Fintype.card_pos (α := Ω)
    exact_mod_cast this
  have hnn : ∀ b : Bool, 0 ≤ prb Y b := by
    intro b
    unfold prb
    positivity
  have hsum : prb Y true + prb Y false = 1 := by
    have hfib : ∑ b : Bool, (fiber Y b).card = Fintype.card Ω := by
      have h := Finset.card_eq_sum_card_fiberwise
        (f := Y) (s := (Finset.univ : Finset Ω)) (t := (Finset.univ : Finset Bool))
        (fun x _ => Finset.mem_univ (Y x))
      rw [Finset.card_univ] at h
      unfold fiber
      exact h.symm
    have h1 : ∑ b : Bool, prb Y b = 1 := by
      unfold prb
      rw [← Finset.sum_div]
      have hc : ∑ b : Bool, ((fiber Y b).card : ℝ) = (Fintype.card Ω : ℝ) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hfib
      rw [hc]
      field_simp
    rw [Fintype.sum_bool] at h1
    exact h1
  have hHY : H Y = Real.negMulLog (prb Y true) + Real.negMulLog (prb Y false) := by
    unfold H
    rw [Fintype.sum_bool]
  have hfalse : prb Y false = 1 - prb Y true := by linarith
  have hhalf : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
    unfold Real.negMulLog
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    ring
  constructor
  · intro heq
    by_contra hne
    have hxy : prb Y true ≠ prb Y false := by
      rw [hfalse]
      intro h
      exact hne (by linarith)
    have hsc := Real.strictConcaveOn_negMulLog.2 (Set.mem_Ici.mpr (hnn true))
      (Set.mem_Ici.mpr (hnn false)) hxy (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num)
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hsc
    have hmid : (1/2 : ℝ) * prb Y true + (1/2 : ℝ) * prb Y false = 1/2 := by linarith
    rw [hmid, hhalf] at hsc
    rw [hHY] at heq
    linarith
  · intro hp
    rw [hHY, hp, hfalse, hp, show (1 : ℝ) - 1/2 = 1/2 by norm_num, hhalf]
    ring
