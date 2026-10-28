-- Prove2me | solution 1 for MeasureEquivalenceRigidity.measureReal_bad_set_le_of_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:46:56.200816+00:00
-- url     : https://prove2.me/submissions/8e68cdbe-8df5-4d79-8bde-e8a0f991f685

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.OrderClosed

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

/-!
The countable-roots step in the manuscript's quasi-invariance rigidity argument.

This module is a helper for Theorems 1.3 and 1.4. It does not assert the
ergodic decomposition, affinity estimate, or representation construction.
The hypotheses below are precisely the quantitative component estimates
needed after those analytic steps have been established.
-/
open Filter MeasureTheory
open scoped Topology ENNReal
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem solution
    [IsProbabilityMeasure μ] (A : Y → ℝ) (B : Set Y)
    (hB : MeasurableSet B) (hA : Integrable A μ)
    (hA_le : ∀ᵐ y ∂μ, A y ≤ 1)
    (hzero : ∀ᵐ y ∂μ, y ∈ B → A y = 0)
    (ε : ℝ) (hmean : 1 - ε ≤ ∫ y, A y ∂μ) :
    μ.real B ≤ ε := by
  have hI : Integrable (B.indicator (fun _ : Y => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hdef : Integrable (fun y => 1 - A y) μ :=
    (integrable_const (1 : ℝ)).sub hA
  have hcomp : B.indicator (fun _ : Y => (1 : ℝ)) ≤ᵐ[μ] fun y => 1 - A y := by
    filter_upwards [hA_le, hzero] with y hy hz
    by_cases hmem : y ∈ B
    · simp [Set.indicator_of_mem hmem, hz hmem]
    · simp only [Set.indicator_of_notMem hmem]
      exact sub_nonneg.mpr hy
  have hle := integral_mono_ae hI hdef hcomp
  rw [integral_indicator_const (1 : ℝ) hB,
    integral_sub (integrable_const (1 : ℝ)) hA] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  linarith
