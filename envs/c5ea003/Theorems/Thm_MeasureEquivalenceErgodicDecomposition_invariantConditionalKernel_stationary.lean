-- Prove2me | Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_stationary
-- name    : MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_stationary
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:58:51.703801+00:00
-- url     : https://prove2.me/theorems/8865eb97-fab0-4c4c-a5c8-e40f23ea241c
-- title:
--   Stationarity of invariant conditional probabilities
-- statement:
--   Let $G$ act measurably on a standard Borel space $Z$, let $\mu$ be finite, and let $P$ be a stationary Markov kernel for $\mu$. Assume $P$ almost surely preserves membership in every measurable $G$-invariant set. If $\kappa_x$ denotes the conditional probability over the invariant sigma-algebra, then $$P_*\kappa_x=\kappa_x\quad\text{for }\mu\text{-almost every }x.$$ This makes the same kernel available on almost every component.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_stationary in InvariantKernelStationarity.lean, lines 47–93; local source SHA-256 62721313e060231e02d9f8d973e232d06346d6b625f9f1c62e28ba99ab16aebc. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp
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

/-! A stationary Markov kernel that does not cross invariant sets is
stationary on almost every actual invariant conditional probability. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]
    (P : Kernel Z Z) [IsMarkovKernel P]

theorem MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_stationary
    (hstat : P ∘ₘ μ = μ)
    (hleak : ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z => g • z) ⁻¹' B = B) →
      ∀ᵐ z ∂μ, ∀ᵐ w ∂P z, w ∈ B ↔ z ∈ B) :
    ∀ᵐ x ∂μ, P ∘ₘ invariantConditionalKernel (G := G) μ x =
      invariantConditionalKernel (G := G) μ x := by sorry
