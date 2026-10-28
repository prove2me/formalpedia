-- Prove2me | Theorems.Thm_MeasureEquivalenceEquidecomposition_exists_piecewise_measure_transport
-- name    : MeasureEquivalenceEquidecomposition.exists_piecewise_measure_transport
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:56:26.177384+00:00
-- url     : https://prove2.me/theorems/adc70dfa-0393-4dbc-87d1-36112037b6a3
-- title:
--   A countable equidecomposition gives inverse measure transports
-- statement:
--   Let measurable disjoint families $(C_n)$ and $(T_n)$ cover sets $A$ and $B$ modulo a measure $\mu$, with $C_n\subseteq A$ and $T_n\subseteq B$. Suppose measurable automorphisms $e_n:X\to X$ preserve $\mu$ and satisfy $e_n(C_n)=T_n$. Then there are measurable transports $F,H:X\to X$ such that
--   $$F_*(\mu|_A)=\mu|_B,\qquad H_*(\mu|_B)=\mu|_A,$$
--   $$F|_{C_n}=e_n|_{C_n},\qquad H|_{T_n}=e_n^{-1}|_{T_n},$$
--   and $H\circ F$ and $F\circ H$ equal the identity almost everywhere on their respective restricted measures. These maps yield genuine pullback unitaries on $L^2$.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceEquidecomposition.exists_piecewise_measure_transport in PiecewiseMeasureTransport.lean, lines 35–103; local source SHA-256 2edb1f31b6c71d14b0e796241b6d1bfb11745945cc8578d8c8cd9b2f5df444a1. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

theorem MeasureEquivalenceEquidecomposition.exists_piecewise_measure_transport
    (μ : Measure X) (A B : Set X) (C T : ℕ → Set X)
    (hCm : ∀ n, MeasurableSet (C n)) (hTm : ∀ n, MeasurableSet (T n))
    (hCsub : ∀ n, C n ⊆ A) (hTsub : ∀ n, T n ⊆ B)
    (hCdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hTdis : Pairwise (fun i j => Disjoint (T i) (T j)))
    (hcoverA : μ (A \ ⋃ n, C n) = 0) (hcoverB : μ (B \ ⋃ n, T n) = 0)
    (e : ℕ → X ≃ᵐ X) (he : ∀ n, MeasurePreserving (e n) μ μ)
    (himage : ∀ n, (e n) '' C n = T n) :
    ∃ F H : X → X,
      MeasurePreserving F (μ.restrict A) (μ.restrict B) ∧
      MeasurePreserving H (μ.restrict B) (μ.restrict A) ∧
      (∀ n, EqOn F (e n) (C n)) ∧ (∀ n, EqOn H (e n).symm (T n)) ∧
      (∀ᵐ x ∂μ.restrict A, H (F x) = x) ∧
      (∀ᵐ x ∂μ.restrict B, F (H x) = x) := by sorry
