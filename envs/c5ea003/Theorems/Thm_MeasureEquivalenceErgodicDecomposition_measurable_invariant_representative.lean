-- Prove2me | Theorems.Thm_MeasureEquivalenceErgodicDecomposition_measurable_invariant_representative
-- name    : MeasureEquivalenceErgodicDecomposition.measurable_invariant_representative
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:57:08.950166+00:00
-- url     : https://prove2.me/theorems/2f81af2a-2e76-40bb-a373-215cca946226
-- title:
--   Almost-everywhere invariant functions admit exactly invariant representatives
-- statement:
--   Let a countable group $G$ act by measurable maps on a measurable space $Z$, and let $\mu$ be a measure. If a measurable real function $f$ satisfies
--   $$f(gz)=f(z)\quad\text{for }\mu\text{-almost every }z\quad(g\in G),$$
--   then there is a function $\widetilde f$ measurable for the exactly invariant sigma-algebra such that $\widetilde f=f$ almost everywhere. This supplies invariant representatives for conditional-expectation arguments without requiring nonsingularity as an extra hypothesis.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceErgodicDecomposition.measurable_invariant_representative in InvariantRepresentatives.lean, lines 13–49; local source SHA-256 a89cf2534ee44edcddd411cf0a6ca63e12dfb71e80ec144f37daaf36bbbeb342. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Condexp

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

/-! Almost-everywhere invariant measurable functions have exactly invariant
measurable representatives for countable group actions. -/
open MeasureTheory ProbabilityTheory Set Filter
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z] [MulAction G Z]
    (μ : Measure Z)

theorem MeasureEquivalenceErgodicDecomposition.measurable_invariant_representative (f : Z → ℝ) (hf : Measurable f)
    (haction : ∀ g : G, Measurable (fun z : Z => g • z))
    (hinv : ∀ g : G, (fun z => f (g • z)) =ᵐ[μ] f) :
    ∃ f' : Z → ℝ, Measurable[invariantSigma (G := G)] f' ∧ f' =ᵐ[μ] f := by sorry
