-- Prove2me | Theorems.Thm_MeasureEquivalenceMarkov_setIntegral_eq_mul_of_kernelAverage_limit
-- name    : MeasureEquivalenceMarkov.setIntegral_eq_mul_of_kernelAverage_limit
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:59:23.240931+00:00
-- url     : https://prove2.me/theorems/4e8e6b53-0c29-42ec-9ce3-6839b53d5c3f
-- title:
--   Integrals from constant kernel-average limits
-- statement:
--   Let $\nu$ be finite, $P$ a Markov kernel, and $s\subseteq Z$ a set such that $\nu|_s$ is stationary. Let $f$ be measurable with $|f|\le C$ for some $C\ge0$. Suppose a strictly increasing subsequence of the Cesaro kernel averages of $f$ converges $\nu$-almost everywhere to a constant $c$. Then $$\int_s f\,d\nu=c\nu(s).$$ This converts componentwise average limits into factorization identities.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceMarkov.setIntegral_eq_mul_of_kernelAverage_limit in KernelAverages.lean, lines 122–153; local source SHA-256 7754096b8d5c878189682abb644ab03a806ab19d770cf142b4f0566759158b05. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
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

/-! Actual bounded kernel iterates, Cesaro averages, and almost-everywhere
subsequences of their Hilbert mean-ergodic limits. -/
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]

theorem MeasureEquivalenceMarkov.setIntegral_eq_mul_of_kernelAverage_limit
    (ν : Measure Z) [IsFiniteMeasure ν] (P : Kernel Z Z) [IsMarkovKernel P]
    (s : Set Z) (hstationary : P ∘ₘ (ν.restrict s) = ν.restrict s)
    (f : Z → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C)
    (ns : ℕ → ℕ) (hns : StrictMono ns) (c : ℝ)
    (hlimit : ∀ᵐ z ∂ν, Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 c)) :
    (∫ z in s, f z ∂ν) = c * ν.real s := by sorry
