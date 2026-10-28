-- Prove2me | solution 1 for MeasureEquivalenceHellinger.affinity_compProd
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:22:32.087984+00:00
-- url     : https://prove2.me/submissions/0320fd9d-3bd0-4fea-b799-fa2150e994b6

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerKernel
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

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







theorem integrable_affinity_integrand (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun y => Real.sqrt (μ.rnDeriv (μ + ν) y).toReal *
      Real.sqrt (ν.rnDeriv (μ + ν) y).toReal) (μ + ν) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (root μ (μ + ν)) (root ν (μ + ν))).congr
  filter_upwards [root_coe μ (μ + ν), root_coe ν (μ + ν)] with y hμ hν
  rw [hμ, hν]
  simp [mul_comm]













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

theorem joint_rnDeriv_of_kernel_ac (hac : ∀ x, κ x ≪ η x) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      (fun p => κ.rnDeriv η p.1 p.2) := by
  have hk : η.withDensity (κ.rnDeriv η) = κ := by
    ext x : 1
    exact Kernel.withDensity_rnDeriv_eq (hac x)
  have hD : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    rw [← Measure.compProd_withDensity (κ.measurable_rnDeriv η), hk]
  have h := (μ ⊗ₘ η).rnDeriv_withDensity (κ.measurable_rnDeriv η)
  rw [← hD] at h
  exact h







theorem affinity_kernel_fiber (x : X) :
    (∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x)) = affinity (κ x) (η x) := by
  rw [affinity_integral]
  apply integral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x),
    η.rnDeriv_eq_rnDeriv_measure (η := κ+η) (a := x)] with y hk he
  simp only [kernelAffinityIntegrand, hk, he]
  rfl





end MeasureEquivalenceHellinger

end

/-! Actual disintegration of Hellinger affinity for equal-marginal kernels. -/
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ η : Kernel X Y) [IsFiniteKernel κ] [IsFiniteKernel η]

theorem solution :
    affinity (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫ x, affinity (κ x) (η x) ∂μ := by
  have hk : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ (κ+η)) =ᵐ[μ ⊗ₘ (κ+η)]
      fun p => κ.rnDeriv (κ+η) p.1 p.2 :=
    joint_rnDeriv_of_kernel_ac μ κ (κ+η)
      (fun x => Measure.AbsolutelyContinuous.rfl.add_right (η x))
  have he : (μ ⊗ₘ η).rnDeriv (μ ⊗ₘ (κ+η)) =ᵐ[μ ⊗ₘ (κ+η)]
      fun p => η.rnDeriv (κ+η) p.1 p.2 :=
    joint_rnDeriv_of_kernel_ac μ η (κ+η)
      (fun x => Measure.AbsolutelyContinuous.rfl.add_right' (κ x))
  have hf : (fun p => Real.sqrt ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ (κ+η)) p).toReal *
      Real.sqrt ((μ ⊗ₘ η).rnDeriv (μ ⊗ₘ (κ+η)) p).toReal) =ᵐ[μ ⊗ₘ (κ+η)]
        kernelAffinityIntegrand κ η := by
    filter_upwards [hk, he] with p hkp hep
    simp only [kernelAffinityIntegrand, hkp, hep]
  have hI : Integrable (kernelAffinityIntegrand κ η) (μ ⊗ₘ (κ+η)) := by
    have h := integrable_affinity_integrand (μ ⊗ₘ κ) (μ ⊗ₘ η)
    rw [← Measure.compProd_add_right] at h
    exact h.congr hf
  calc
    affinity (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫ p, kernelAffinityIntegrand κ η p ∂(μ ⊗ₘ (κ+η)) := by
      rw [affinity_integral, ← Measure.compProd_add_right]
      exact integral_congr_ae hf
    _ = ∫ x, ∫ y, kernelAffinityIntegrand κ η (x,y) ∂((κ+η) x) ∂μ :=
      Measure.integral_compProd hI
    _ = _ := integral_congr_ae (Eventually.of_forall (affinity_kernel_fiber κ η))
