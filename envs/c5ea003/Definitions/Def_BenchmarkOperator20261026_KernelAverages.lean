-- Prove2me | Definitions.Def_BenchmarkOperator20261026_KernelAverages
-- name    : BenchmarkOperator20261026_KernelAverages
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:31:33.952529+00:00
-- url     : https://prove2.me/theorems/67cbf792-a292-4500-8278-b2a5a1342cdb
-- title:
--   Kernel Averages
-- statement:
--   Defines pointwise integration by a kernel, its iterates, and their Cesaro averages. These are the explicit functions used in the subsequent mean-ergodic and componentwise convergence theorems.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization KernelAverages.lean, lines 14–21; source SHA-256 7754096b8d5c878189682abb644ab03a806ab19d770cf142b4f0566759158b05. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def kernelApply (P : Kernel Z Z) (f : Z → ℝ) (z : Z) : ℝ := ∫ y, f y ∂P z

noncomputable def kernelIterate (P : Kernel Z Z) (f : Z → ℝ) : ℕ → Z → ℝ
  | 0 => f
  | n + 1 => kernelApply P (kernelIterate P f n)

noncomputable def kernelAverage (P : Kernel Z Z) (f : Z → ℝ) (n : ℕ) (z : Z) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, kernelIterate P f k z

























section L2

variable (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ)
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hL : ∀ f : Lp ℝ 2 μ, L f =ᵐ[μ] kernelApply P f)

include hstationary hL







end L2

end MeasureEquivalenceMarkov


