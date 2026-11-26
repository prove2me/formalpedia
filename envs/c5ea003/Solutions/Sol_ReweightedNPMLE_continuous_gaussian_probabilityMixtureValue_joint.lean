-- Prove2me | solution 1 for ReweightedNPMLE.continuous_gaussian_probabilityMixtureValue_joint
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:08:00.144191+00:00
-- url     : https://prove2.me/submissions/62b0fddc-b8af-4edf-9e83-d11046d7a9b2

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

-- Inline helpers preserved from ReweightedNPMLE.ParameterizedProbabilityIntegral.
section
/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

theorem continuous_probabilityIntegral_with_parameter {X Θ : Type*}
    [TopologicalSpace X] [TopologicalSpace Θ] [CompactSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (F : X → C(Θ, ℝ)) (hF : Continuous F) :
    Continuous (fun p : X × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hfixed : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂q.2)
      (𝓝 p) (𝓝 (∫ a, F p.1 a ∂p.2)) :=
    ((ProbabilityMeasure.continuous_integral_continuousMap (F p.1)).comp
      continuous_snd).continuousAt
  have hnorm : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖)
      (𝓝 p) (𝓝 0) := by
    have hh : Continuous (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖) :=
      ((hF.comp continuous_fst).sub continuous_const).norm
    have hh' : Tendsto (fun q : X × ProbabilityMeasure Θ ↦ ‖F q.1 - F p.1‖)
        (𝓝 p) (𝓝 ‖F p.1 - F p.1‖) := hh.continuousAt
    simpa only [sub_self, norm_zero] using hh'
  have herr : Tendsto (fun q : X × ProbabilityMeasure Θ ↦
      ∫ a, (F q.1 - F p.1) a ∂q.2) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm _ hnorm
    intro q
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (q.2 : Measure Θ))
        (Eventually.of_forall (fun a ↦ (F q.1 - F p.1).norm_coe_le_norm a)))
  have hidentity (q : X × ProbabilityMeasure Θ) :
      (∫ a, (F q.1 - F p.1) a ∂q.2) + (∫ a, F p.1 a ∂q.2) =
        ∫ a, F q.1 a ∂q.2 := by
    have h₁ := (F q.1).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (q.2 : Measure Θ))
    have h₂ := (F p.1).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := (q.2 : Measure Θ))
    simp only [ContinuousMap.sub_apply]
    rw [integral_sub h₁ h₂]
    ring
  simpa only [hidentity, zero_add] using herr.add hfixed









end ReweightedNPMLE
end

/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦
      probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1 i) (θ a)) p.2) := by
  have hk (y : Point d) : Continuous (fun a : Θ ↦ gaussianKernel d y (θ a)) := by
    have hpair : Continuous (fun a : Θ ↦ (y, θ a)) := continuous_const.prodMk hθ
    have hh : Continuous ((fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2) ∘
        (fun a : Θ ↦ (y, θ a))) :=
      (continuous_gaussianKernel d).comp hpair
    simpa only [Function.comp_apply] using hh
  let F : Point d → C(Θ, ℝ) := fun y ↦ ⟨fun a ↦ gaussianKernel d y (θ a), hk y⟩
  have huncurry : Continuous (fun p : Point d × Θ ↦ F p.1 p.2) := by
    have hpair : Continuous (fun p : Point d × Θ ↦ (p.1, θ p.2)) :=
      continuous_fst.prodMk (hθ.comp continuous_snd)
    have hh : Continuous ((fun z : Point d × Point d ↦ gaussianKernel d z.1 z.2) ∘
        (fun p : Point d × Θ ↦ (p.1, θ p.2))) :=
      (continuous_gaussianKernel d).comp hpair
    exact hh
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F huncurry
  apply continuous_pi
  intro i
  have hmap : Continuous (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦ (p.1 i, p.2)) :=
    ((continuous_apply i).comp continuous_fst).prodMk continuous_snd
  have hh : Continuous ((fun p : Point d × ProbabilityMeasure Θ ↦ ∫ a, F p.1 a ∂p.2) ∘
      (fun p : (Fin n → Point d) × ProbabilityMeasure Θ ↦ (p.1 i, p.2))) :=
    (continuous_probabilityIntegral_with_parameter F hF).comp hmap
  exact hh
