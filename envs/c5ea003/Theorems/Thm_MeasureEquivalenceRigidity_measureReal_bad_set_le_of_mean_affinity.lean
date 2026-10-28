-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_measureReal_bad_set_le_of_mean_affinity
-- name    : MeasureEquivalenceRigidity.measureReal_bad_set_le_of_mean_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:08:33.976779+00:00
-- url     : https://prove2.me/theorems/fc4f4701-fdc5-4101-afdc-bcb993f7eac9
-- title:
--   A mean affinity deficit bounds the bad set
-- statement:
--   Let $\mu$ be a probability measure, $B$ a measurable set, and $A$ an integrable real function with $A\leq1$ almost everywhere and $A=0$ almost everywhere on $B$. If
--   $$1-\varepsilon\leq\int A\,d\mu,$$
--   then $\mu(B)\leq\varepsilon$. No lower bound on $A$ is needed. This elementary estimate turns an averaged affinity bound into a bound on the exceptional component set.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.measureReal_bad_set_le_of_mean_affinity in RigidityRoots.lean, lines 22–46; local source SHA-256 2065c065a8ef889655833f9182163ac012be4432afb18eec37736d74e9464056. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

theorem MeasureEquivalenceRigidity.measureReal_bad_set_le_of_mean_affinity
    [IsProbabilityMeasure μ] (A : Y → ℝ) (B : Set Y)
    (hB : MeasurableSet B) (hA : Integrable A μ)
    (hA_le : ∀ᵐ y ∂μ, A y ≤ 1)
    (hzero : ∀ᵐ y ∂μ, y ∈ B → A y = 0)
    (ε : ℝ) (hmean : 1 - ε ≤ ∫ y, A y ∂μ) :
    μ.real B ≤ ε := by sorry
