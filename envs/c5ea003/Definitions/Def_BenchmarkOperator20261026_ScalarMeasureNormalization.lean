-- Prove2me | Definitions.Def_BenchmarkOperator20261026_ScalarMeasureNormalization
-- name    : BenchmarkOperator20261026_ScalarMeasureNormalization
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:48:43.2635+00:00
-- url     : https://prove2.me/theorems/ab68f145-c28b-4430-851f-e9297325e5a2
-- title:
--   Scalar Measure Normalization
-- statement:
--   Constructs the unitary from $L^2(c\mu;\mathbb C)$ to $L^2(\mu;\mathbb C)$ for nonzero nonnegative real $c$ and sigma-finite $\mu$. The retained absolute-continuity facts justify using the Radon–Nikodym equivalence in this definition.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization ScalarMeasureNormalization.lean, lines 12–23; source SHA-256 b8afebd7384f449bb141da550b113155b3aa38061def3b92e5b5fad0cb4430bb. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]

theorem scalar_smul_absolutelyContinuous (c : ℝ≥0) : c • μ ≪ μ := by
  change (c : ℝ≥0∞) • μ ≪ μ
  exact Measure.smul_absolutelyContinuous

theorem scalar_absolutelyContinuous_smul (c : ℝ≥0) (hc : c ≠ 0) : μ ≪ c • μ := by
  change μ ≪ (c : ℝ≥0∞) • μ
  exact Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr hc)

def scalarMeasureEquiv (c : ℝ≥0) (hc : c ≠ 0) :
    Lp ℂ 2 (c • μ) ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  rnWeightedEquiv (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc)







end MeasureUnitary


