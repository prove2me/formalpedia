-- Prove2me | solution 1 for MeasureEquivalenceRigidity.ae_componentQI_of_uniform_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:11:25.893552+00:00
-- url     : https://prove2.me/submissions/7156e48f-0fef-41ef-a003-20bbbe372312

import Definitions.Def_BenchmarkOperator20261026_ComponentQuasiInvariance
import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerKernel
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_MeasureEquivalenceRigidity_ae_componentQI_of_real_root_mean_affinity
import Theorems.Thm_MeasureEquivalenceRigidity_tendsto_mean_along_real_roots

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

-- Preserved source skeleton: HellingerAffinity
section
/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Y : Type*} [MeasurableSpace Y]









theorem affinity_nonneg (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    0 ≤ affinity μ ν := by
  rw [affinity_integral]
  apply integral_nonneg
  intro y
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)





theorem affinity_le_one (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : affinity μ ν ≤ 1 := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  calc
    affinity μ ν ≤ ‖root μ (μ + ν)‖ * ‖root ν (μ + ν)‖ := real_inner_le_norm _ _
    _ = 1 := by rw [root_probability_norm μ _ hμ, root_probability_norm ν _ hν, mul_one]





end MeasureEquivalenceHellinger

end

-- Preserved source skeleton: HellingerKernel
section
/-! Actual disintegration of Hellinger affinity for equal-marginal kernels. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]







theorem kernelAffinityIntegrand_measurable : Measurable (kernelAffinityIntegrand κ η) :=
  (κ.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt.mul
    (η.measurable_rnDeriv (κ+η)).ennreal_toReal.sqrt

theorem affinity_kernel_fiber (x : X) :
    (∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) = affinity (κ x) (η x) := by
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x),
    η.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x)] with y hk he
  simp only [kernelAffinityIntegrand, hk, he]
  rfl

theorem kernelAffinity_measurable : Measurable (fun x => affinity (κ x) (η x)) := by
  have h := (kernelAffinityIntegrand_measurable κ η).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ+η)
  have he : (fun x => ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) =
      fun x => affinity (κ x) (η x) := funext (affinity_kernel_fiber κ η)
  rw [he] at h
  exact h.measurable



end MeasureEquivalenceHellinger

end

/-! Actual component quasi-invariance is detected by Hellinger affinity,
and vanishing mean deficits along roots give component quasi-invariance. -/
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceHellinger MeasureEquivalenceErgodicDecomposition
variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (η : Measure Y) [IsProbabilityMeasure η]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem solution
    (g : ℝ →+ Additive K)
    (hzero : ∀ᵐ y ∂η, ∀ k : K,
      affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ y,
        affinity (κ y) ((κ y).map (fun z => Additive.toMul (g b) • z)) ∂η)
    (a : ℝ) :
    ∀ᵐ y ∂η, Additive.toMul (g a) ∈ componentQI κ y := by
  let F : ℝ → ℝ := fun b => ∫ y,
    affinity (κ y) ((κ y).map (fun z => Additive.toMul (g b) • z)) ∂η
  have hFle : ∀ b, F b ≤ 1 := by
    intro b
    have hle : ∀ y, affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z)) ≤ 1 := by
      intro y
      letI : IsProbabilityMeasure ((κ y).map (fun z => Additive.toMul (g b) • z)) :=
        (κ y).isProbabilityMeasure_map (measurable_const_smul _).aemeasurable
      exact affinity_le_one _ _
    have hm : Measurable (fun y => affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z))) := by
      simpa only [Kernel.map_apply _ (measurable_const_smul _)] using
        kernelAffinity_measurable κ (κ.map (fun z => Additive.toMul (g b) • z))
    have hi : Integrable (fun y => affinity (κ y)
        ((κ y).map (fun z => Additive.toMul (g b) • z))) η :=
      Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
        (Eventually.of_forall (fun y => by
          simpa only [Real.norm_eq_abs, abs_of_nonneg (affinity_nonneg _ _)] using hle y))
    simpa only [F, integral_const, probReal_univ, one_smul] using
      integral_mono_ae hi (integrable_const (1 : ℝ)) (Eventually.of_forall hle)
  have hlim := tendsto_mean_along_real_roots F hFle hsmall a
  apply ae_componentQI_of_real_root_mean_affinity η κ g a hzero
    (fun n => 1 - F (a / ((n+1 : ℕ) : ℝ)))
  · intro n
    change 1 - (1 - F _) ≤ F _
    linarith
  · simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hlim
