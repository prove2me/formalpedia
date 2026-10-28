-- Prove2me | solution 1 for MeasureEquivalenceDensity.squareMeasure_continuous
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:14:26.753172+00:00
-- url     : https://prove2.me/submissions/884d11b3-28ab-4dff-9b15-354d1ab9c5dd

import Definitions.Def_BenchmarkOperator20261026_DensityMeasure
import Definitions.Def_BenchmarkOperator20261026_DensitySquare
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Tactic
import Theorems.Thm_MeasureEquivalenceDensity_square_continuous

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

-- Preserved source skeleton: DensityMeasure
section
/-! Concrete finite measures with an L2 square density. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)









theorem squareMeasure_integral (f : Lp ℝ 2 μ) (g : α → ℝ) :
    ∫ x, g x ∂(squareMeasure μ f : Measure α) = ∫ x, f x ^ 2 * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp [ENNReal.toReal_ofReal, sq_nonneg, smul_eq_mul]



end MeasureEquivalenceDensity

end

/-! Concrete finite measures with an L2 square density. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
open MeasureEquivalenceDensity
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem solution [TopologicalSpace α] [BorelSpace α] :
    Continuous (squareMeasure μ) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro g
  let gLp : Lp ℝ ∞ μ := (g.memLp_top (μ := μ)).toLp g
  let B : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 1 1
  have hEq : (fun f : Lp ℝ 2 μ => ∫ x, g x ∂(squareMeasure μ f : Measure α)) =
      fun f => ∫ x, (B gLp (square μ f)) x ∂μ := by
    funext f
    rw [squareMeasure_integral]
    apply integral_congr_ae
    filter_upwards [square_coe μ f, (g.memLp_top (μ := μ)).coeFn_toLp,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) gLp (square μ f)]
      with x h1 h2 h3
    change f x ^ 2 * g x = ((ContinuousLinearMap.mul ℝ ℝ).holder 1 gLp (square μ f)) x
    rw [h3]
    change f x ^ 2 * g x = gLp x * (square μ f) x
    change gLp x = g x at h2
    rw [h1, h2, mul_comm]
  rw [hEq]
  exact continuous_integral.comp ((B gLp).continuous.comp (square_continuous μ))
