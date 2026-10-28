-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
-- name    : BenchmarkOperator20261026_MeasureCantorTuple
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:32:05.895475+00:00
-- url     : https://prove2.me/theorems/c0a5ef12-a0e1-4385-b8b6-5894881ebe46
-- title:
--   Measure Cantor Tuple
-- statement:
--   Defines Cantor space, its countable clopen cylinder family, and the unit-modulus phase equal to $1$ on a cylinder and $-1$ off it. The retained measurability, unit-norm and generating-family facts make these phases available for later multiplication representations.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureCantorTuple.lean, lines 13–64; source SHA-256 b32b4da27193dab3bbb85a9a9e93a136cc0ccc409d41eb23326027ccd2332f72. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
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

/-! Countably many genuine L² multiplication unitaries, one for every
clopen finite-coordinate Cantor cylinder. Equivalent measures give
intertwining representations through the actual RN unitary. -/

open MeasureTheory Set

namespace MeasureUnitary

abbrev CantorSpace := ℕ → Bool
abbrev CantorCylinderIndex := Σ s : Finset ℕ, Set (∀ i : s, Bool)

instance _root_.MeasureUnitary.instCountableCantorCylinderIndex : Countable CantorCylinderIndex := inferInstance

def cantorCylinder (k : CantorCylinderIndex) : Set CantorSpace :=
  cylinder k.1 k.2

theorem cantorCylinder_measurable (k : CantorCylinderIndex) : MeasurableSet (cantorCylinder k) := by
  exact (Set.to_countable k.2).measurableSet.cylinder

noncomputable def cantorCylinderPhase (k : CantorCylinderIndex) (x : CantorSpace) : ℂ :=
  by classical exact if x ∈ cantorCylinder k then 1 else -1

theorem cantorCylinderPhase_measurable (k : CantorCylinderIndex) : Measurable (cantorCylinderPhase k) := by
  classical
  exact Measurable.ite (cantorCylinder_measurable k) measurable_const measurable_const

theorem cantorCylinderPhase_norm (k : CantorCylinderIndex) (x : CantorSpace) :
    ‖cantorCylinderPhase k x‖ = 1 := by
  classical
  unfold cantorCylinderPhase
  split_ifs <;> norm_num







theorem cantorCylinder_range : Set.range cantorCylinder = measurableCylinders (fun _ : ℕ => Bool) := by
  ext s
  constructor
  · rintro ⟨⟨I, S⟩, rfl⟩
    exact cylinder_mem_measurableCylinders _ _ (Set.to_countable S).measurableSet
  · intro hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    exact ⟨⟨I, S⟩, rfl⟩

theorem cantorCylinder_generates :
    MeasurableSpace.generateFrom (Set.range cantorCylinder) = (inferInstance : MeasurableSpace CantorSpace) := by
  rw [cantorCylinder_range, generateFrom_measurableCylinders]



end MeasureUnitary


