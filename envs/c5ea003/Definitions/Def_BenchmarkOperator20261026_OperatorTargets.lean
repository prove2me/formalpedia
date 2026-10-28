-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorTargets
-- name    : BenchmarkOperator20261026_OperatorTargets
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:31:13.929648+00:00
-- url     : https://prove2.me/theorems/997854a0-2959-4b1f-8f5a-9dedf406b78c
-- title:
--   Relations and Borel structure for the operator comparison
-- statement:
--   Defines the canonical complex Hilbert space $\ell_2(\mathbb N)$, Cantor space, bounded operators and their strong-operator Borel structure. It also defines mutual absolute continuity, Borel reduction, strict Borel reduction, and the proposition asserting the strict operator comparison. The representation-comparison chain is not part of this retained bundle.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorTargets.lean, lines 18–76; source SHA-256 d1549f6c814c1d9bc6f14b1f80a9834c95484a58ba6efcf7d94a853f4491c3b5. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorNormalization
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

/-!
Exact target propositions for Theorems 1.3 and 1.4 of MeasureEquivalence.tex.
These are definitions of the outstanding goals, not proofs of those goals.
The operator topology is strong convergence on vectors. Representations are
all group homomorphisms to the genuine strong unitary group.
-/

open MeasureTheory

namespace OperatorCoding

noncomputable section

abbrev CanonicalHilbert := lp (fun _ : ℕ => ℂ) 2
abbrev Cantor := ℕ → Bool
abbrev CanonicalOperator := CanonicalHilbert →L[ℂ] CanonicalHilbert


/-- The SOT on all bounded operators, specified without changing the norm
topology that Mathlib also uses on continuous linear maps. -/
abbrev operatorStrongTopology : TopologicalSpace CanonicalOperator :=
  TopologicalSpace.induced
    (fun T : CanonicalOperator => fun x : CanonicalHilbert => T x) inferInstance

abbrev operatorBorel : MeasurableSpace CanonicalOperator :=
  @borel CanonicalOperator operatorStrongTopology





def MeasureEquivalent (μ ν : ProbabilityMeasure Cantor) : Prop :=
  (μ : Measure Cantor) ≪ (ν : Measure Cantor) ∧ (ν : Measure Cantor) ≪ (μ : Measure Cantor)



/-- Borel reducibility with the two measurable structures explicit. This
prevents accidental use of the operator-norm Borel structure. -/
def BorelReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, @Measurable X Y mX mY f ∧ ∀ x y, E x y ↔ F (f x) (f y)



def BorelStrictlyReducesWith {X Y : Type*} (mX : MeasurableSpace X) (mY : MeasurableSpace Y)
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducesWith mX mY E F ∧ ¬ BorelReducesWith mY mX F E



/-- Exact Theorem 1.3 on the canonical separable infinite-dimensional Hilbert
space. This proposition is deliberately not asserted as a theorem. -/
def Theorem13 : Prop :=
  BorelStrictlyReducesWith inferInstance operatorBorel
    MeasureEquivalent OperatorUnitaryEquivalent



end
end OperatorCoding


