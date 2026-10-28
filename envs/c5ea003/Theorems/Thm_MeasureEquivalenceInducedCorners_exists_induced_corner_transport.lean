-- Prove2me | Theorems.Thm_MeasureEquivalenceInducedCorners_exists_induced_corner_transport
-- name    : MeasureEquivalenceInducedCorners.exists_induced_corner_transport
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:00:58.022414+00:00
-- url     : https://prove2.me/theorems/4cd0262e-c9d2-40c3-9d05-a1d6f5906ae7
-- title:
--   Transports between equal finite induced corners
-- statement:
--   Let a countable group $G$ act ergodically and measure-preservingly on a sigma-finite measurable space $(Z,\mu)$; assume the group has measurable singletons. Let $A,B$ be measurable with $\mu(A)=\mu(B)<\infty$. On $Z\times G$, with corner measures $(\mu|_A)\times\#G$ and $(\mu|_B)\times\#G$, there are inverse almost-everywhere measure-preserving transports $F,H$. The map $F$ preserves the induced orbit point and commutes almost everywhere with every left index shift. This realizes the corner equivalence by actual measurable maps.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceInducedCorners.exists_induced_corner_transport in InducedCornerTransport.lean, lines 93–173; local source SHA-256 62c274462557d556c2eb9fa9d7c218cee0ea0903508ec157c0f483c6a91d6df9. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
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

/-! Genuine finite-corner induced-module transports on the product of
the base sample space and the counting-measure group coordinate. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
open MeasureEquivalenceInducedCorners
open MeasureEquivalenceEquidecomposition
variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
variable (μ : Measure Z) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp

theorem MeasureEquivalenceInducedCorners.exists_induced_corner_transport
    (herg : ∀ s : Set Z, MeasurableSet s →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0)
    (A B : Set Z) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfin : μ A ≠ ∞) (hmass : μ A = μ B) :
    ∃ F H : (Z × G) → (Z × G),
      MeasurePreserving F (cornerMeasure μ A) (cornerMeasure μ B) ∧
      MeasurePreserving H (cornerMeasure μ B) (cornerMeasure μ A) ∧
      (∀ᵐ p ∂cornerMeasure μ A, H (F p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ B, F (H p) = p) ∧
      (∀ᵐ p ∂cornerMeasure μ A, orbitPoint (F p) = orbitPoint p) ∧
      (∀ h : G, ∀ᵐ p ∂cornerMeasure μ A,
        F (indexShift h p) = indexShift h (F p)) := by sorry
