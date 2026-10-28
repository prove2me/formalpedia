-- Prove2me | Theorems.Thm_MeasureEquivalenceRestrictedProduct_aeconst_of_dense_translation_invariant
-- name    : MeasureEquivalenceRestrictedProduct.aeconst_of_dense_translation_invariant
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:02:25.644985+00:00
-- url     : https://prove2.me/theorems/c1d7803b-f278-4d6b-836b-18fbfa8a7ee4
-- title:
--   Dense translation invariance forces a measurable set to be null or conull
-- statement:
--   Let $G$ be a Hausdorff, pseudo-metrizable, sigma-compact topological abelian group with its Borel sigma-algebra. Let $\mu$ be a locally finite, s-finite translation-invariant measure, and let $D\subseteq G$ be dense. If a measurable set $E$ satisfies
--   $$(x\mapsto x+d)^{-1}E=E\pmod\mu\qquad(d\in D),$$
--   then its indicator is almost everywhere constant. Equivalently, $E$ is null or conull. This is the dense rational-translation ergodicity fact used on finite-dimensional fibers.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRestrictedProduct.aeconst_of_dense_translation_invariant in DenseEventErgodic.lean, lines 28–56; local source SHA-256 b0208c3133d1a249a9c2c2986ef81a8036b1137265889a24790f6c83073e1693. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen

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

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [PseudoMetrizableSpace G] [SigmaCompactSpace G]

theorem MeasureEquivalenceRestrictedProduct.aeconst_of_dense_translation_invariant (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [SFinite μ] [μ.IsAddLeftInvariant]
    (D : Set G) (hD : Dense D) (E : Set G) (hE : MeasurableSet E)
    (hinv : ∀ q ∈ D, (fun x => x + q) ⁻¹' E =ᵐ[μ] E) :
    EventuallyConst E (ae μ) := by sorry
