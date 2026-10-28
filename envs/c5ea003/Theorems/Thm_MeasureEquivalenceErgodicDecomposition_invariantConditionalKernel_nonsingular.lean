-- Prove2me | Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_nonsingular
-- name    : MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_nonsingular
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:59:54.369822+00:00
-- url     : https://prove2.me/theorems/69222b97-da00-4bb4-9d44-231e1a174fae
-- title:
--   Nonsingularity on invariant conditional probabilities
-- statement:
--   Let $G$ act measurably on a countably generated standard Borel space $Z$, and let $\mu$ be finite. If the action of a fixed $g\in G$ is quasi-measure-preserving for $\mu$, then its invariant conditional probabilities satisfy $$g_*\kappa_x\ll\kappa_x\quad\text{for }\mu\text{-almost every }x.$$ This transfers global nonsingularity to the actual conditional measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_nonsingular in InvariantConditional.lean, lines 154–172; local source SHA-256 18db8be10608de97d850984b7c4ff8902f00cffb313850ed50d0a0f207f194dd. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

theorem MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_nonsingular
    [MeasurableSpace.CountablyGenerated Z]
    (g : G) (hg : Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ) :
    ∀ᵐ z ∂μ,
      (invariantConditionalKernel (G := G) μ z).map (fun w => g • w) ≪
        invariantConditionalKernel (G := G) μ z := by sorry
