-- Prove2me | Theorems.Thm_MeasureEquivalenceEquidecomposition_exists_equidecomposition
-- name    : MeasureEquivalenceEquidecomposition.exists_equidecomposition
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T10:55:49.337041+00:00
-- url     : https://prove2.me/theorems/33fd939e-fb45-4cf8-aa0c-339477534cc6
-- title:
--   Measurable equidecomposition of equal finite-mass sets
-- statement:
--   Let a countable group $G$ act measurably and preserve a measure $\mu$ on $Z$. Assume the action is ergodic: every exactly invariant measurable set is null or conull. If measurable sets $A,B\subseteq Z$ have the same finite measure, then there are group elements $g_n$ and pairwise disjoint measurable pieces $C_n\subseteq A$, $T_n\subseteq B$ such that
--   $$T_n=g_nC_n,\qquad
--   \mu\!\left(A\setminus\bigcup_n C_n\right)=\mu\!\left(B\setminus\bigcup_n T_n\right)=0.$$
--   Thus equal finite-mass corners can be matched by orbit translations.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceEquidecomposition.exists_equidecomposition in ErgodicEquidecomposition.lean, lines 213–244; local source SHA-256 48cd93d9f8184c96c4f262e912499b9b0697c6de2b398bcc7b37b41157b272b0. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Group.MeasurableEquiv
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

/-! Greedy measurable equidecomposition for finite equal-mass sets under
an actual ergodic, measure-preserving action of a countable group. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
open MeasureEquivalenceEquidecomposition
open MeasureEquivalenceRigidity
variable {G Z : Type*} [Group G] [MulAction G Z]
variable [MeasurableSpace Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)
include hmp

theorem MeasureEquivalenceEquidecomposition.exists_equidecomposition [Countable G]
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ (e : ℕ → G) (C T : ℕ → Set Z),
      (∀ n, MeasurableSet (C n) ∧ MeasurableSet (T n)) ∧
      (∀ n, C n ⊆ A ∧ T n ⊆ B) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      Pairwise (fun i j => Disjoint (T i) (T j)) ∧
      (∀ n, T n = (fun z : Z => (e n)⁻¹ • z) ⁻¹' C n) ∧
      μ (A \ ⋃ n, C n) = 0 ∧ μ (B \ ⋃ n, T n) = 0 := by sorry
