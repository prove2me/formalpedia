-- Prove2me | solution 1 for FiniteRateDistortion.distortion_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:39:36.05075+00:00
-- url     : https://prove2.me/submissions/31f92fc6-61da-46e9-a761-ca82ab1c502d

-- Sol generated from Bridges/FiniteRateDistortion/Core.lean
import Mathlib
import Definitions.Def_Bridges_FiniteRateDistortion_Core

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





/-- The joint distribution is normalised. -/
theorem joint_sum_eq_one (μ : FinProbDist α) (W : Channel α β) :
    ∑ a, ∑ b, μ.mass a * W.prob a b = 1 := by
  have h : ∀ a : α, ∑ b, μ.mass a * W.prob a b = μ.mass a := by
    intro a; rw [← Finset.mul_sum, W.prob_sum_one a, mul_one]
  simp_rw [h]
  exact μ.mass_sum_one


/-! ## The elementary entropy estimate -/



/-! ## Mutual information and distortion -/






/-! ## The rate–distortion function and its Lagrangian dual -/









open FiniteRateDistortion in
theorem solution(μ : FinProbDist α) (d : α → β → ℝ) (W : Channel α β) :
    -distortionBudget d ≤ distortion μ d W := by
  have hle : ∀ a : α, ∀ b : β, -distortionBudget d ≤ d a b := by
    intro a b
    have h1 : |d a b| ≤ ∑ b', |d a b'| :=
      Finset.single_le_sum (f := fun b' => |d a b'|) (fun b' _ => abs_nonneg _)
        (Finset.mem_univ b)
    have h2 : ∑ b', |d a b'| ≤ distortionBudget d :=
      Finset.single_le_sum (f := fun a' => ∑ b', |d a' b'|)
        (fun a' _ => Finset.sum_nonneg fun b' _ => abs_nonneg _) (Finset.mem_univ a)
    have h3 : -(d a b) ≤ |d a b| := neg_le_abs _
    linarith
  have hterm : ∀ a : α, ∀ b : β,
      μ.mass a * W.prob a b * (-distortionBudget d) ≤ μ.mass a * W.prob a b * d a b := by
    intro a b
    exact mul_le_mul_of_nonneg_left (hle a b)
      (mul_nonneg (μ.mass_nonneg a) (W.prob_nonneg a b))
  have hsum : ∑ a : α, ∑ b : β, μ.mass a * W.prob a b * (-distortionBudget d)
      = -distortionBudget d := by
    have h1 : ∀ a : α, ∑ b : β, μ.mass a * W.prob a b * (-distortionBudget d)
        = (∑ b : β, μ.mass a * W.prob a b) * (-distortionBudget d) := by
      intro a; rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun a _ => h1 a), ← Finset.sum_mul, joint_sum_eq_one, one_mul]
  calc -distortionBudget d
      = ∑ a : α, ∑ b : β, μ.mass a * W.prob a b * (-distortionBudget d) := hsum.symm
    _ ≤ distortion μ d W :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
