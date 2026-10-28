-- Prove2me | solution 1 for MeasureEquivalenceHellinger.affinity_eq_zero_iff_mutuallySingular
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:28:44.06025+00:00
-- url     : https://prove2.me/submissions/e4a0500d-3bd4-4594-8116-c20b12011ef5

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/
open MeasureTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {Y : Type*} [MeasurableSpace Y]

theorem solution (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : affinity μ ν = 0 ↔ μ ⟂ₘ ν := by
  have hμ : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hν : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  constructor
  · intro ha
    rw [affinity_integral] at ha
    have haz := (integral_eq_zero_iff_of_nonneg
      (fun y => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (integrable_affinity_integrand μ ν)).mp ha
    have hprod : ∀ᵐ y ∂(μ + ν),
        μ.rnDeriv (μ + ν) y = 0 ∨ ν.rnDeriv (μ + ν) y = 0 := by
      filter_upwards [haz, Measure.rnDeriv_ne_top μ (μ + ν),
        Measure.rnDeriv_ne_top ν (μ + ν)] with y hy hμt hνt
      rcases mul_eq_zero.mp hy with h | h
      · left
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          ((Real.sqrt_eq_zero ENNReal.toReal_nonneg).mp h)).resolve_right hμt
      · right
        exact ((ENNReal.toReal_eq_zero_iff _).mp
          ((Real.sqrt_eq_zero ENNReal.toReal_nonneg).mp h)).resolve_right hνt
    let s : Set Y := {y | μ.rnDeriv (μ + ν) y = 0}
    have hsm : MeasurableSet s := (Measure.measurable_rnDeriv _ _) (measurableSet_singleton 0)
    have hμs : μ s = 0 := by
      rw [← Measure.withDensity_rnDeriv_eq μ (μ + ν) hμ,
        withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
      have hempty : {y | μ.rnDeriv (μ + ν) y ≠ 0} ∩ s = ∅ := by
        ext y
        simp [s]
      rw [hempty, measure_empty]
    have hνsc : ν sᶜ = 0 := by
      rw [← Measure.withDensity_rnDeriv_eq ν (μ + ν) hν,
        withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
      have hset : {x | ν.rnDeriv (μ + ν) x ≠ 0} ∩ sᶜ =
          {x | ¬ (μ.rnDeriv (μ + ν) x = 0 ∨ ν.rnDeriv (μ + ν) x = 0)} := by
        ext y
        simp [s, and_comm]
      rw [hset]
      exact ae_iff.mp hprod
    exact ⟨s, hsm, hμs, hνsc⟩
  · intro hs
    rw [affinity_integral]
    apply integral_eq_zero_of_ae
    apply ae_add_measure_iff.mpr
    constructor
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular hs.symm hμ] with y hy
      simp [hy]
    · filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular hs hν] with y hy
      simp [hy]
