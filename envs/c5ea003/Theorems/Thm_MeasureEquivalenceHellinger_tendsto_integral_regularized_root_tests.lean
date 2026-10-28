-- Prove2me | Theorems.Thm_MeasureEquivalenceHellinger_tendsto_integral_regularized_root_tests
-- name    : MeasureEquivalenceHellinger.tendsto_integral_regularized_root_tests
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:00:40.470904+00:00
-- url     : https://prove2.me/theorems/935305ab-df6a-4427-a516-e58494f11ff9
-- title:
--   Convergence of regularized square-root tests
-- statement:
--   Let $\rho$ be finite and let $P,Q:Z\to[0,1]$ be measurable. For the positive regularizers $\varepsilon_n$ tending to zero, put $f_n=(\sqrt Q+\varepsilon_n)/(\sqrt P+\varepsilon_n)$. Then $$\int\frac{P f_n+Q f_n^{-1}}2\,d\rho\longrightarrow\int\sqrt P\sqrt Q\,d\rho.$$ The regularizers are the explicit sequence fixed in the formal definition.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceHellinger.tendsto_integral_regularized_root_tests in HellingerVariational.lean, lines 136–177; local source SHA-256 c912bd1ce1e9bc61a95e175790951c084090a95c68b9bc6ff7ab523c087cde29. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerVariational
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Semicontinuity.Basic

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

/-! Continuous positive test functions for Hellinger affinity. -/
open MeasureTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger

theorem MeasureEquivalenceHellinger.tendsto_integral_regularized_root_tests
    {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z) [IsFiniteMeasure ρ]
    (P Q : Z → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (hPbound : ∀ z, 0 ≤ P z ∧ P z ≤ 1)
    (hQbound : ∀ z, 0 ≤ Q z ∧ Q z ≤ 1) :
    Tendsto (fun n => ∫ z,
      (P z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n)) +
       Q z * ((Real.sqrt (Q z) + regularizer n) / (Real.sqrt (P z) + regularizer n))⁻¹) / 2 ∂ρ)
      atTop (𝓝 (∫ z, Real.sqrt (P z) * Real.sqrt (Q z) ∂ρ)) := by sorry
