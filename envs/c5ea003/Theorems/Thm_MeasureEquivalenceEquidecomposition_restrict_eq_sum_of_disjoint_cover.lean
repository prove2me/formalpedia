-- Prove2me | Theorems.Thm_MeasureEquivalenceEquidecomposition_restrict_eq_sum_of_disjoint_cover
-- name    : MeasureEquivalenceEquidecomposition.restrict_eq_sum_of_disjoint_cover
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:55:59.335643+00:00
-- url     : https://prove2.me/theorems/11acb7d7-6b57-49cc-9fdf-439df39574f5
-- title:
--   A disjoint measurable cover decomposes the restricted measure
-- statement:
--   Let $\mu$ be a measure on a measurable space $X$, let $A\subseteq X$, and let $(C_n)$ be pairwise disjoint measurable subsets of $A$. If their union covers $A$ modulo a null set, then
--   $$\mu|_A=\sum_{n=0}^{\infty}\mu|_{C_n}.$$
--   No finiteness assumption on $\mu$ or measurability assumption on $A$ is required. The identity turns a countable equidecomposition into a measure-transport formula.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceEquidecomposition.restrict_eq_sum_of_disjoint_cover in PiecewiseMeasureTransport.lean, lines 15–33; local source SHA-256 2edb1f31b6c71d14b0e796241b6d1bfb11745945cc8578d8c8cd9b2f5df444a1. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

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

/-! Countable equidecompositions give actual measure-preserving maps
with almost-everywhere inverses, and therefore genuine complex L2 unitaries. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
open MeasureEquivalenceEquidecomposition
variable {X : Type*} [MeasurableSpace X]

theorem MeasureEquivalenceEquidecomposition.restrict_eq_sum_of_disjoint_cover (μ : Measure X) (A : Set X)
    (C : ℕ → Set X) (hCm : ∀ n, MeasurableSet (C n))
    (hCsub : ∀ n, C n ⊆ A)
    (hCdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : μ (A \ ⋃ n, C n) = 0) :
    μ.restrict A = Measure.sum (fun n => μ.restrict (C n)) := by sorry
