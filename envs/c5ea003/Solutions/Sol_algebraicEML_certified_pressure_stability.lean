-- Prove2me | solution 1 for algebraicEML_certified_pressure_stability
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:51:47.46296+00:00
-- url     : https://prove2.me/submissions/187b9f72-6e58-4efc-9750-bd608109e637

import Mathlib
import Definitions.Def_Bridges_PosetTheory_AlgebraicEMLThermodynamicFormalism

open Finset Real in
theorem solution {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (φ ψ : α → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (h : ∀ a, |φ a - ψ a| ≤ ρ) :
    |closurePressure β φ - closurePressure β ψ| ≤ |β| * ρ := by
  have key : ∀ f g : α → ℝ, (∀ a, |f a - g a| ≤ ρ) →
      closurePressure β f ≤ closurePressure β g + |β| * ρ := by
    intro f g hfg
    unfold closurePressure closurePartitionFunction closureWeight
    have hpos : 0 < ∑ a : α, Real.exp (β * g a) :=
      Finset.sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
    have hpos' : 0 < ∑ a : α, Real.exp (β * f a) :=
      Finset.sum_pos (fun a _ => Real.exp_pos _) univ_nonempty
    have hle : ∑ a : α, Real.exp (β * f a) ≤ Real.exp (|β| * ρ) * ∑ a : α, Real.exp (β * g a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : β * (f a - g a) ≤ |β| * ρ := by
        refine le_trans (le_abs_self _) ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hfg a) (abs_nonneg β)
      linarith
    calc Real.log (∑ a, Real.exp (β * f a))
        ≤ Real.log (Real.exp (|β| * ρ) * ∑ a, Real.exp (β * g a)) := Real.log_le_log hpos' hle
      _ = |β| * ρ + Real.log (∑ a, Real.exp (β * g a)) := by
          rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
      _ = Real.log (∑ a, Real.exp (β * g a)) + |β| * ρ := by ring
  rw [abs_le]
  constructor
  · have := key ψ φ (fun a => by rw [abs_sub_comm]; exact h a)
    linarith
  · have := key φ ψ h
    linarith
