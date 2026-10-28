-- Prove2me | Theorems.Thm_MeasureUnitary_exists_faithful_L2
-- name    : MeasureUnitary.exists_faithful_L2
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:10:44.929753+00:00
-- url     : https://prove2.me/theorems/ff8f9cb9-3a81-4553-8cda-b9ed57accd00
-- title:
--   Every sigma-finite measure has an almost-everywhere nonzero $L^2$ vector
-- statement:
--   For every sigma-finite measure $\mu$ on a measurable space $X$, there exists a complex $L^2(\mu)$ vector $f$ such that
--   $$f(x)\ne0\quad\text{for }\mu\text{-almost every }x.$$
--   Such a vector is faithful: its squared-norm density has exactly the same null sets as $\mu$. It is used to recover a maximal pushforward measure class from vector states.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureUnitary.exists_faithful_L2 in VectorSpectralState.lean, lines 53–67; local source SHA-256 91cf85685c9b39a58c792c41443686f066e3760b3d0b3abd17aec51928bc9287. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
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

/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]

theorem MeasureUnitary.exists_faithful_L2 (μ : Measure Ω) [SigmaFinite μ] :
    ∃ f : Lp ℂ 2 μ, ∀ᵐ x ∂μ, f x ≠ 0 := by sorry
