-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_absolutelyContinuous_or_mutuallySingular_of_ergodic
-- name    : MeasureEquivalenceRigidity.absolutelyContinuous_or_mutuallySingular_of_ergodic
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:08:19.321992+00:00
-- url     : https://prove2.me/theorems/a9cab763-fcf4-4e58-9e20-5d7dc4611bb2
-- title:
--   An ergodic measure is dominated by or singular to a nonsingular measure
-- statement:
--   Let a countable group $G$ act on a measurable space $Y$. Suppose every group translation is quasi-measure-preserving for a measure $\nu$, and suppose a measure $\mu$ is ergodic for exactly invariant measurable sets. Then
--   $$\mu\ll\nu\quad\text{or}\quad\mu\perp\nu.$$
--   Invariance of either measure is not assumed. This dichotomy identifies the alternatives used for conditional component measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.absolutelyContinuous_or_mutuallySingular_of_ergodic in NonsingularDichotomy.lean, lines 38–69; local source SHA-256 542243f64d0aebba5102fce77fa9eb04c3dd0f758b75e3476dbe6c2265748e26. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

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
The equivalence-or-singularity dichotomy for ergodic nonsingular measures
of one countable group action. Ergodicity is stated explicitly for
measurable invariant sets; no invariance of the measures is assumed.
-/
open MeasureTheory MeasureTheory.Measure Set
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]

theorem MeasureEquivalenceRigidity.absolutelyContinuous_or_mutuallySingular_of_ergodic
    (μ ν : Measure Y)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0) :
    μ ≪ ν ∨ μ ⟂ₘ ν := by sorry
