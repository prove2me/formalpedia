-- Prove2me | solution 1 for MeasureEquivalenceHellinger.exists_continuous_Icc_integral_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:29:31.384462+00:00
-- url     : https://prove2.me/submissions/b3095357-beb6-4ce0-92a4-3d7fcda6ac32

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

-- Preserved source skeleton: HellingerVariational
section
/-! Continuous positive test functions for Hellinger affinity. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceHellinger



private theorem abs_clip_sub_le (c C u v : ℝ) (hvc : c ≤ v) (hvC : v ≤ C) :
    |max c (min C u) - v| ≤ |u - v| := by
  by_cases huc : u ≤ c
  · have humin : min C u ≤ c := (min_le_right _ _).trans huc
    rw [max_eq_left humin, abs_of_nonpos (sub_nonpos.mpr hvc),
      abs_of_nonpos (sub_nonpos.mpr (huc.trans hvc))]
    linarith
  · by_cases huC : C ≤ u
    · rw [min_eq_left huC, max_eq_right (hvc.trans hvC),
        abs_of_nonneg (sub_nonneg.mpr hvC),
        abs_of_nonneg (sub_nonneg.mpr (hvC.trans huC))]
      linarith
    · rw [min_eq_right (le_of_not_ge huC), max_eq_right (le_of_not_ge huc)]





















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
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]

theorem solution
    (ρ : Measure Z) [IsFiniteMeasure ρ]
    (f : Z → ℝ) (hf : Integrable f ρ)
    (c C : ℝ) (hcC : c ≤ C)
    (hfbound : ∀ z, c ≤ f z ∧ f z ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ g : C(Z, ℝ), (∀ z, c ≤ g z ∧ g z ≤ C) ∧
      (∫ z, ‖f z - g z‖ ∂ρ) ≤ η := by
  obtain ⟨g, hg, _⟩ := hf.exists_boundedContinuous_integral_sub_le hη
  let g' : C(Z, ℝ) :=
    ⟨fun z => max c (min C (g z)), continuous_const.max (continuous_const.min g.continuous)⟩
  refine ⟨g', ?_, ?_⟩
  · intro z
    exact ⟨le_max_left _ _, max_le hcC (min_le_left _ _)⟩
  · have hgi : Integrable g ρ := g.integrable ρ
    have hg'i : Integrable g' ρ := (BoundedContinuousFunction.mkOfCompact g').integrable ρ
    apply le_trans (integral_mono (hf.sub hg'i).norm (hf.sub hgi).norm ?_) hg
    intro z
    change ‖f z - max c (min C (g z))‖ ≤ ‖f z - g z‖
    simpa only [Real.norm_eq_abs, abs_sub_comm (f z)] using
      abs_clip_sub_le c C (g z) (f z) (hfbound z).1 (hfbound z).2
