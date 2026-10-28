-- Prove2me | solution 1 for MeasureEquivalenceRigidity.ae_mem_of_root_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:47:25.820984+00:00
-- url     : https://prove2.me/submissions/3d822382-dc84-46a5-9c93-134fd5caa952

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_MeasureEquivalenceRigidity_measureReal_bad_set_le_of_mean_affinity

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

-- Preserved source skeleton: RigidityRoots
section
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

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}







variable {K : Type*} [AddCommGroup K]

omit [MeasurableSpace Y] in
/-- Failure of membership in an additive subgroup implies failure for
every specified root. This is the bad-set inclusion used in the paper. -/
theorem bad_set_subset_root_bad_set
    (S : Y → AddSubgroup K) (x z : K) (m : ℕ)
    (hroot : m • z = x) :
    {y | x ∉ S y} ⊆ {y | z ∉ S y} := by
  intro y hy hz
  exact hy (hroot ▸ (S y).nsmul_mem hz m)









end MeasureEquivalenceRigidity

end

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
variable {K : Type*} [AddCommGroup K]

theorem solution
    [IsProbabilityMeasure μ]
    (S : Y → AddSubgroup K) (x : K) (root : ℕ → K)
    (multiplicity : ℕ → ℕ)
    (hroot : ∀ n, multiplicity n • root n = x)
    (A : ℕ → Y → ℝ)
    (hbad : ∀ n, MeasurableSet {y | root n ∉ S y})
    (hA : ∀ n, Measurable (A n))
    (hA_nonneg : ∀ n y, 0 ≤ A n y)
    (hA_le : ∀ n y, A n y ≤ 1)
    (hzero : ∀ n, ∀ᵐ y ∂μ, root n ∉ S y → A n y = 0)
    (ε : ℕ → ℝ)
    (hmean : ∀ n, 1 - ε n ≤ ∫ y, A n y ∂μ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ᵐ y ∂μ, x ∈ S y := by
  have hbound : ∀ n, μ.real {y | root n ∉ S y} ≤ ε n := by
    intro n
    apply measureReal_bad_set_le_of_mean_affinity (A n) _ (hbad n) _
      (Eventually.of_forall (hA_le n)) (hzero n) (ε n) (hmean n)
    exact Integrable.mono' (integrable_const (1 : ℝ)) (hA n).aestronglyMeasurable
      (Eventually.of_forall (fun y => by
        simpa [abs_of_nonneg (hA_nonneg n y)] using hA_le n y))
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm
  · apply ge_of_tendsto hε
    apply Eventually.of_forall
    intro n
    exact (measureReal_mono
      (bad_set_subset_root_bad_set S x (root n) (multiplicity n) (hroot n))).trans
        (hbound n)
  · exact measureReal_nonneg
