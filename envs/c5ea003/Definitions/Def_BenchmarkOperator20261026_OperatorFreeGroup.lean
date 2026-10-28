-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
-- name    : BenchmarkOperator20261026_OperatorFreeGroup
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:30:04.933001+00:00
-- url     : https://prove2.me/theorems/8a980181-3e7f-4002-a117-7f012876a932
-- title:
--   Operator Free Group
-- statement:
--   Defines simultaneous conjugacy for a countable tuple of group elements and supplies the pointwise topology instance used on homomorphisms. These objects are used in the later conversion between free-group representations and unitary tuples.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorFreeGroup.lean, lines 15–53; source SHA-256 881e3c4261d5203122c75806f65bd36cf46414676ea977941034efbd2ed0f31f. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic

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
The free-group step in the representation coding argument.  The topology on
homomorphisms is pointwise convergence, and this file applies to every
topological group, including the strong unitary group of a Hilbert space.
-/

namespace OperatorCoding

variable {ι G : Type*} [Group G]

/-- Simultaneous conjugacy of an indexed family in a group. -/
def TupleConjugate (u v : ι → G) : Prop :=
  ∃ w : G, ∀ i, w * u i * w⁻¹ = v i







section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The pointwise topology on group representations. -/
instance representationTopology : TopologicalSpace (FreeGroup ι →* G) :=
  TopologicalSpace.induced (fun ρ : FreeGroup ι →* G => (ρ : FreeGroup ι → G)) inferInstance









end Topological

end OperatorCoding


