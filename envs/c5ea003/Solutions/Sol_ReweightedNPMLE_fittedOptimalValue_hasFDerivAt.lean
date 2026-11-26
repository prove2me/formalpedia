-- Prove2me | solution 1 for ReweightedNPMLE.fittedOptimalValue_hasFDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:01:49.032611+00:00
-- url     : https://prove2.me/submissions/d2d33161-250c-4f42-a066-ce1d7fe04638

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.FittedEnvelope.
section
/-!
# Envelope theorem for fitted likelihood values

The optimized weighted likelihood is a convex function of the weight vector.
The two optimizer inequalities squeeze its first-order remainder between zero
and a product involving the change in the fitted log-vector.  Consequently,
continuity of the fitted log-vector implies that it is the Fréchet derivative
of the optimal-value function.  Combining this envelope argument with the
local Lipschitz estimates from `FittedRegularity` gives the paper's gradient
identity on every locally bounded positive weight box.
-/

open Set Filter Asymptotics
open scoped BigOperators Topology

namespace ReweightedNPMLE







theorem fittedOptimalValue_remainder_nonneg {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    0 ≤ fittedOptimalValue vhat u - fittedOptimalValue vhat w -
      weightedLogLikelihood (u - w) (vhat w) := by
  have hmax := hu.2 (vhat w) hw.1
  unfold fittedOptimalValue weightedLogLikelihood at hmax ⊢
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  linarith

theorem fittedOptimalValue_remainder_le {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    fittedOptimalValue vhat u - fittedOptimalValue vhat w -
        weightedLogLikelihood (u - w) (vhat w) ≤
      ∑ i, (u i - w i) *
        (Real.log (vhat u i) - Real.log (vhat w i)) := by
  have hmax := hw.2 (vhat u) hu.1
  unfold fittedOptimalValue weightedLogLikelihood at hmax ⊢
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  linarith



theorem abs_sum_mul_le_card_mul_norm {n : ℕ}
    (a b : Fin n → ℝ) :
    |∑ i, a i * b i| ≤ (n : ℝ) * ‖a‖ * ‖b‖ := by
  calc
    |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖a‖ * ‖b‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖a‖ * ‖b‖ := by
      simp [mul_assoc]

theorem fittedOptimalValue_remainder_abs_le {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w u : Fin n → ℝ)
    (hw : IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hu : IsMaxOn C (weightedLogLikelihood u) (vhat u)) :
    |fittedOptimalValue vhat u - fittedOptimalValue vhat w -
        weightedLogLikelihood (u - w) (vhat w)| ≤
      (n : ℝ) * ‖u - w‖ *
        ‖(fun i ↦ Real.log (vhat u i)) -
          (fun i ↦ Real.log (vhat w i))‖ := by
  let r := fittedOptimalValue vhat u - fittedOptimalValue vhat w -
    weightedLogLikelihood (u - w) (vhat w)
  let b : Fin n → ℝ := fun i ↦
    Real.log (vhat u i) - Real.log (vhat w i)
  have hr0 : 0 ≤ r := fittedOptimalValue_remainder_nonneg vhat w u hw hu
  have hrle : r ≤ ∑ i, (u i - w i) * b i :=
    fittedOptimalValue_remainder_le vhat w u hw hu
  calc
    |r| = r := abs_of_nonneg hr0
    _ ≤ ∑ i, (u i - w i) * b i := hrle
    _ ≤ |∑ i, (u i - w i) * b i| := le_abs_self _
    _ ≤ (n : ℝ) * ‖u - w‖ * ‖b‖ :=
      abs_sum_mul_le_card_mul_norm (u - w) b
    _ = _ := rfl











end ReweightedNPMLE
end

/-!
# Envelope theorem for fitted likelihood values

The optimized weighted likelihood is a convex function of the weight vector.
The two optimizer inequalities squeeze its first-order remainder between zero
and a product involving the change in the fitted log-vector.  Consequently,
continuity of the fitted log-vector implies that it is the Fréchet derivative
of the optimal-value function.  Combining this envelope argument with the
local Lipschitz estimates from `FittedRegularity` gives the paper's gradient
identity on every locally bounded positive weight box.
-/

open Set Filter Asymptotics
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n : ℕ}
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ)
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (hzcont : ContinuousAt
      (fun u i ↦ Real.log (vhat u i)) w) :
    HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat w i))) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  let z : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun u i ↦ Real.log (vhat u i)
  have hz0 : Tendsto (fun h ↦ z (w + h) - z w) (𝓝 0) (𝓝 0) := by
    have hcomp : ContinuousAt (fun h ↦ z (w + h)) 0 := by
      apply hzcont.comp_of_eq
      · fun_prop
      · simp [z]
    have hconst : ContinuousAt (fun _h : Fin n → ℝ ↦ z w) 0 :=
      continuousAt_const
    have hsub := hcomp.sub hconst
    change Tendsto (fun h ↦ z (w + h) - z w) (𝓝 0)
      (𝓝 (z (w + 0) - z w)) at hsub
    simpa using hsub
  have heps : 0 < c / ((n : ℝ) + 1) := by positivity
  have hevent : ∀ᶠ h : Fin n → ℝ in 𝓝 0,
      ‖z (w + h) - z w‖ < c / ((n : ℝ) + 1) := by
    have hball := hz0 (Metric.ball_mem_nhds (0 : Fin n → ℝ) heps)
    filter_upwards [hball] with h hh
    simpa [Metric.mem_ball, dist_zero] using hh
  filter_upwards [hevent] with h hh
  have hrem := fittedOptimalValue_remainder_abs_le vhat w (w + h)
    (hmax w) (hmax (w + h))
  have hdiff : w + h - w = h := by abel
  have hcoef : (n : ℝ) * ‖z (w + h) - z w‖ ≤ c := by
    have hn : (0 : ℝ) ≤ n := by positivity
    have hnorm : 0 ≤ ‖z (w + h) - z w‖ := norm_nonneg _
    have hnlt : (n : ℝ) < (n : ℝ) + 1 := by linarith
    have := mul_lt_mul_of_pos_left hh (show (0 : ℝ) < n + 1 by positivity)
    rw [div_eq_mul_inv] at this
    have hden : ((n : ℝ) + 1) * (c * ((n : ℝ) + 1)⁻¹) = c := by
      field_simp
    rw [hden] at this
    nlinarith
  rw [fittedLogLinearFunctional_apply]
  have hlikelihood : weightedLogLikelihood h (vhat w) =
      ∑ i, h i * Real.log (vhat w i) := rfl
  rw [← hlikelihood]
  rw [hdiff] at hrem
  change ‖fittedOptimalValue vhat (w + h) - fittedOptimalValue vhat w -
      weightedLogLikelihood h (vhat w)‖ ≤ c * ‖h‖
  rw [Real.norm_eq_abs]
  calc
    |fittedOptimalValue vhat (w + h) - fittedOptimalValue vhat w -
        weightedLogLikelihood h (vhat w)| ≤
        (n : ℝ) * ‖h‖ * ‖z (w + h) - z w‖ := by
      simpa [z] using hrem
    _ = ‖h‖ * ((n : ℝ) * ‖z (w + h) - z w‖) := by ring
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hcoef (norm_nonneg _)
    _ = c * ‖h‖ := mul_comm _ _
