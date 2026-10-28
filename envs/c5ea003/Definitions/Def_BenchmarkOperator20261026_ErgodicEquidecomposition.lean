-- Prove2me | Definitions.Def_BenchmarkOperator20261026_ErgodicEquidecomposition
-- name    : BenchmarkOperator20261026_ErgodicEquidecomposition
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:27:51.209267+00:00
-- url     : https://prove2.me/theorems/bc622931-1308-4299-bdfe-c97dfb0922f0
-- title:
--   Ergodic Equidecomposition
-- statement:
--   Defines a greedy matching step and the successive source remainders, matched pieces and target pieces for a countable orbit matching. These recursive objects are used in the later theorem producing a measurable equidecomposition of equal finite-mass sets.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization ErgodicEquidecomposition.lean, lines 38–52; source SHA-256 48cd93d9f8184c96c4f262e912499b9b0697c6de2b398bcc7b37b41157b272b0. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

open MeasureEquivalenceRigidity

variable {G Z : Type*} [Group G] [MulAction G Z]



/-- One stage keeps precisely the unmatched source and target points. -/
def greedyStep (e : ℕ → G) (n : ℕ) (p : Set Z × Set Z) : Set Z × Set Z :=
  let C := p.1 ∩ (fun z : Z => e n • z) ⁻¹' p.2
  (p.1 \ C, p.2 \ ((fun z : Z => (e n)⁻¹ • z) ⁻¹' C))

def greedyRemainder (e : ℕ → G) (A B : Set Z) : ℕ → Set Z × Set Z
  | 0 => (A, B)
  | n+1 => greedyStep e n (greedyRemainder e A B n)

def greedyPiece (e : ℕ → G) (A B : Set Z) (n : ℕ) : Set Z :=
  (greedyRemainder e A B n).1 ∩
    (fun z : Z => e n • z) ⁻¹' (greedyRemainder e A B n).2

def greedyTarget (e : ℕ → G) (A B : Set Z) (n : ℕ) : Set Z :=
  (fun z : Z => (e n)⁻¹ • z) ⁻¹' greedyPiece e A B n



















section Measure

variable [MeasurableSpace Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)

include hmp











end Measure

end MeasureEquivalenceEquidecomposition


