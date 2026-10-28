-- Prove2me | solution 1 for MeasureEquivalenceHellinger.affinity_le_affinityTest_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:29:00.391496+00:00
-- url     : https://prove2.me/submissions/7387a996-8110-4fb9-8439-446d70888612

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic

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

-- Preserved source skeleton: HellingerVariational
section
/-! Continuous positive test functions for Hellinger affinity. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceHellinger

private theorem sqrt_product_le_test (p q f : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hf : 0 < f) : Real.sqrt p * Real.sqrt q ≤ (f * p + f⁻¹ * q) / 2 := by
  have hid : f * p + f⁻¹ * q - 2 * (Real.sqrt p * Real.sqrt q) =
      (f * Real.sqrt p - Real.sqrt q) ^ 2 / f := by
    rw [sub_sq, mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
    field_simp
    ring
  have hnonneg := div_nonneg (sq_nonneg (f * Real.sqrt p - Real.sqrt q)) hf.le
  rw [← hid] at hnonneg
  linarith























section Compact

variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]



























end Compact

end MeasureEquivalenceHellinger

end

/-! Continuous positive test functions for Hellinger affinity. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger

theorem solution
    {Z : Type*} [MeasurableSpace Z]
    (μ ν : Measure Z) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : Z → ℝ) (hfpos : ∀ z, 0 < f z)
    (hfμ : Integrable f μ) (hfinvν : Integrable (fun z => (f z)⁻¹) ν) :
    affinity μ ν ≤ affinityTest μ ν f := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hiP := (integrable_toReal_rnDeriv_mul_iff hμ).mpr hfμ
  have hiQ := (integrable_toReal_rnDeriv_mul_iff hν).mpr hfinvν
  rw [affinity_integral]
  calc
    _ ≤ ∫ z, ((μ.rnDeriv (μ + ν) z).toReal * f z +
        (ν.rnDeriv (μ + ν) z).toReal * (f z)⁻¹) / 2 ∂(μ + ν) := by
      apply integral_mono (integrable_affinity_integrand μ ν) ((hiP.add hiQ).div_const 2)
      intro z
      simpa only [mul_comm] using sqrt_product_le_test
        (μ.rnDeriv (μ + ν) z).toReal (ν.rnDeriv (μ + ν) z).toReal (f z)
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg (hfpos z)
    _ = affinityTest μ ν f := by
      rw [integral_div, integral_add hiP hiQ,
        integral_toReal_rnDeriv_mul hμ, integral_toReal_rnDeriv_mul hν]
      rfl
