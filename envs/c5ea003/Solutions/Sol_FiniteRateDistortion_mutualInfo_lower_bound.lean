-- Prove2me | solution 1 for FiniteRateDistortion.mutualInfo_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:16.180962+00:00
-- url     : https://prove2.me/submissions/052702c8-6798-4b65-a275-4dd62dfee9db

-- Sol generated from Bridges/FiniteRateDistortion/Core.lean
import Mathlib
import Definitions.Def_Bridges_FiniteRateDistortion_Core
import Theorems.Thm_FiniteRateDistortion_neg_div_exp_one_le_mul_log_div

/-!
# Finite rate–distortion theory: channels, mutual information, and the Lagrangian dual

This module supplies the objects used by
`Bridges/FiniteRateDistortion/TropicalEnvelope.lean`, which referred to a finite
rate-distortion vocabulary that no module in the catalog provided.

Everything is finite and elementary:

* `FinProbDist α`, `Channel α β` — a source distribution and a test channel;
* `mutualInfo`, `distortion` — the two functionals of a channel;
* `rateDistortion μ d D` — the infimum of the mutual information over channels meeting
  the distortion constraint;
* `lagrangianDual μ d s` — the infimum of `I(W) + s · d(W)`;
* `lagrangianDual_le_rateDistortion` — **weak duality**: `Φ(s) - s·D ≤ R(D)` for every
  slope `s ≥ 0`, the affine lower bound whose tropical envelope is studied downstream.

The only analytic input is the elementary estimate `w · log (w / q) ≥ -q/e`
(`neg_div_exp_one_le_mul_log_div`), which makes the Lagrangian set bounded below, so the
infima are genuine.
-/

open Finset

noncomputable section

open FiniteRateDistortion

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## Sources and channels -/




theorem outMass_nonneg (μ : FinProbDist α) (W : Channel α β) (b : β) : 0 ≤ outMass μ W b :=
  Finset.sum_nonneg fun a _ => mul_nonneg (μ.mass_nonneg a) (W.prob_nonneg a b)

/-- The joint distribution is normalised. -/
theorem joint_sum_eq_one (μ : FinProbDist α) (W : Channel α β) :
    ∑ a, ∑ b, μ.mass a * W.prob a b = 1 := by
  have h : ∀ a : α, ∑ b, μ.mass a * W.prob a b = μ.mass a := by
    intro a; rw [← Finset.mul_sum, W.prob_sum_one a, mul_one]
  simp_rw [h]
  exact μ.mass_sum_one

/-- The output distribution is normalised. -/
theorem sum_outMass_eq_one (μ : FinProbDist α) (W : Channel α β) :
    ∑ b, outMass μ W b = 1 := by
  unfold outMass
  rw [Finset.sum_comm]
  exact joint_sum_eq_one μ W

/-! ## The elementary entropy estimate -/



/-! ## Mutual information and distortion -/






/-! ## The rate–distortion function and its Lagrangian dual -/









open FiniteRateDistortion in
theorem solution(μ : FinProbDist α) (W : Channel α β) :
    -(1 / Real.exp 1) ≤ mutualInfo μ W := by
  have hterm : ∀ a : α, ∀ b : β,
      -(μ.mass a * (outMass μ W b / Real.exp 1))
        ≤ μ.mass a * W.prob a b * Real.log (W.prob a b / outMass μ W b) := by
    intro a b
    have h := neg_div_exp_one_le_mul_log_div (w := W.prob a b) (q := outMass μ W b)
      (W.prob_nonneg a b) (outMass_nonneg μ W b)
    have h2 := mul_le_mul_of_nonneg_left h (μ.mass_nonneg a)
    calc -(μ.mass a * (outMass μ W b / Real.exp 1))
        = μ.mass a * -(outMass μ W b / Real.exp 1) := by ring
      _ ≤ μ.mass a * (W.prob a b * Real.log (W.prob a b / outMass μ W b)) := h2
      _ = μ.mass a * W.prob a b * Real.log (W.prob a b / outMass μ W b) := by ring
  have key : ∀ a : α, ∑ b, -(μ.mass a * (outMass μ W b / Real.exp 1))
      = -(μ.mass a * (1 / Real.exp 1)) := by
    intro a
    have h1 : ∑ b, -(μ.mass a * (outMass μ W b / Real.exp 1))
        = -(μ.mass a / Real.exp 1) * ∑ b, outMass μ W b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [h1, sum_outMass_eq_one]
    ring
  have hsum : ∑ a : α, ∑ b : β, -(μ.mass a * (outMass μ W b / Real.exp 1))
      = -(1 / Real.exp 1) := by
    rw [Finset.sum_congr rfl (fun a _ => key a)]
    have h2 : ∑ a : α, -(μ.mass a * (1 / Real.exp 1))
        = -(1 / Real.exp 1) * ∑ a : α, μ.mass a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [h2, μ.mass_sum_one, mul_one]
  calc -(1 / Real.exp 1)
      = ∑ a : α, ∑ b : β, -(μ.mass a * (outMass μ W b / Real.exp 1)) := hsum.symm
    _ ≤ mutualInfo μ W :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
