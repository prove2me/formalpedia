-- Prove2me | Theorems.Thm_MeasureEquivalenceErgodicDecomposition_exists_constant_average_limit_on_components
-- name    : MeasureEquivalenceErgodicDecomposition.exists_constant_average_limit_on_components
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:58:10.93625+00:00
-- url     : https://prove2.me/theorems/2ee46b93-3711-4cf3-96e3-4fe2530d50f1
-- title:
--   A common averaging subsequence is constant on almost every invariant component
-- statement:
--   Let a countable group act measurably and nonsingularly on a nonempty standard Borel space $Z$, and let $\mu$ be finite. Let $K_x$ be the invariant conditional kernel and $P$ the concrete stationary Metropolis kernel formed from an enumeration of the group moves. For every measurable representative $f\in L^2(\mu;\mathbb R)$, for $\mu$-almost every $x$ there are a strictly increasing sequence $(n_k)$ and $c\in\mathbb R$ such that
--   $$\frac1{n_k}\sum_{j<n_k}P^jf(z)\longrightarrow c
--   \quad\text{for }K_x\text{-almost every }z.$$
--   This componentwise constant limit is the mean-ergodic input to the ergodicity of the conditional measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceErgodicDecomposition.exists_constant_average_limit_on_components in ErgodicComponents.lean, lines 32–69; local source SHA-256 9fe06b1ffe866eb70025b7c2163316471a3071431befd8f7709fc9a0ece1e5e1. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_GroupMarkov
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_KernelAverages
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
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

/-! Actual ergodicity of almost every invariant conditional probability,
using one global Markov contraction and a mean-ergodic subsequence. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceMarkov
variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableEq Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

omit [MeasurableEq Z]

theorem MeasureEquivalenceErgodicDecomposition.exists_constant_average_limit_on_components (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c : ℝ,
      ∀ᵐ z ∂invariantConditionalKernel (G := G) μ x,
        Tendsto (fun n => kernelAverage
          (metropolisKernel μ (groupMoves (G := G)) (groupMoves_ac μ hns)) f (ns n) z)
          atTop (𝓝 c) := by sorry
