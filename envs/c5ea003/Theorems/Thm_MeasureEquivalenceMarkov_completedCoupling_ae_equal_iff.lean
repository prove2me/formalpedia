-- Prove2me | Theorems.Thm_MeasureEquivalenceMarkov_completedCoupling_ae_equal_iff
-- name    : MeasureEquivalenceMarkov.completedCoupling_ae_equal_iff
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:57:22.320246+00:00
-- url     : https://prove2.me/theorems/58717eaa-60ad-4ea8-a8d0-d03984db2408
-- title:
--   The completed orbit coupling detects invariance
-- statement:
--   Let $e$ be a measurable automorphism of $Z$, and let $\mu,\nu$ be measures with the same null sets. Form the completed coupling by taking the $\nu$-weighted graph of $e^{-1}$, its transposed graph, and the prescribed diagonal remainder. For every measurable real function $f$,
--   $$f(x)=f(y)\quad\text{for coupling-almost every }(x,y)
--   \quad\Longleftrightarrow\quad
--   f(z)=f(e^{-1}z)\quad\mu\text{-almost everywhere}.$$
--   The diagonal completion does not change the invariant functions detected by the graph edges.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceMarkov.completedCoupling_ae_equal_iff in MetropolisCoupling.lean, lines 105–133; local source SHA-256 5dd4c9054ac0ec7fd9b84a78437c0872889d3343d7cfeb4991d7d2011bc25e51. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
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

/-! Explicit stationary couplings from overlap measures along a
measurable automorphism. Their edges detect invariance. -/
open MeasureTheory Filter
open scoped ENNReal
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]

theorem MeasureEquivalenceMarkov.completedCoupling_ae_equal_iff
    (μ ν : Measure Z) (e : Z ≃ᵐ Z)
    (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (f : Z → ℝ) (hf : Measurable f) :
    (∀ᵐ z ∂completedCoupling μ ν e, f z.1 = f z.2) ↔
      ∀ᵐ z ∂μ, f z = f (e.symm z) := by sorry
