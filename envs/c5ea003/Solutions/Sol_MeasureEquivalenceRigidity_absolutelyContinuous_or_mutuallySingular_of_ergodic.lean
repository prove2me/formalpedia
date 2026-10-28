-- Prove2me | solution 1 for MeasureEquivalenceRigidity.absolutelyContinuous_or_mutuallySingular_of_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:46:10.867999+00:00
-- url     : https://prove2.me/submissions/475fd383-1ec0-4136-8de1-ee18a7679825

import Definitions.Def_BenchmarkOperator20261026_NonsingularDichotomy
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

-- Preserved source skeleton: NonsingularDichotomy
section
/-!
The equivalence-or-singularity dichotomy for ergodic nonsingular measures
of one countable group action. Ergodicity is stated explicitly for
measurable invariant sets; no invariance of the measures is assumed.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace MeasureEquivalenceRigidity

variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]



omit [Countable G] [MeasurableSpace Y] in
theorem subset_orbitSaturation (s : Set Y) : s ⊆ orbitSaturation (G := G) s := by
  intro y hy
  exact mem_iUnion.mpr ⟨1, by simpa using hy⟩

omit [Countable G] [MeasurableSpace Y] in
theorem preimage_orbitSaturation (s : Set Y) (h : G) :
    (fun y => h • y) ⁻¹' orbitSaturation (G := G) s = orbitSaturation (G := G) s := by
  ext y
  constructor
  · intro hy
    rcases mem_iUnion.mp hy with ⟨g, hg⟩
    exact mem_iUnion.mpr ⟨g * h, by simpa [mul_smul] using hg⟩
  · intro hy
    rcases mem_iUnion.mp hy with ⟨g, hg⟩
    exact mem_iUnion.mpr ⟨g * h⁻¹, by simpa [mul_smul] using hg⟩





end MeasureEquivalenceRigidity

end

/-!
The equivalence-or-singularity dichotomy for ergodic nonsingular measures
of one countable group action. Ergodicity is stated explicitly for
measurable invariant sets; no invariance of the measures is assumed.
-/
open MeasureTheory MeasureTheory.Measure Set
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
variable {G Y : Type*} [Group G] [Countable G]
    [MeasurableSpace Y] [MulAction G Y]

theorem solution
    (μ ν : Measure Y)
    (hνns : ∀ g : G, QuasiMeasurePreserving (fun y : Y => g • y) ν ν)
    (hμerg : ∀ s : Set Y, MeasurableSet s →
      (∀ g : G, (fun y => g • y) ⁻¹' s = s) → μ s = 0 ∨ μ sᶜ = 0) :
    μ ≪ ν ∨ μ ⟂ₘ ν := by
  classical
  by_cases hμν : μ ≪ ν
  · exact Or.inl hμν
  right
  change ¬ (∀ ⦃s : Set Y⦄, ν s = 0 → μ s = 0) at hμν
  push Not at hμν
  obtain ⟨s, hνs, hμs⟩ := hμν
  let t := toMeasurable ν s
  have htm : MeasurableSet t := measurableSet_toMeasurable _ _
  have hνt : ν t = 0 := (measure_toMeasurable s).trans hνs
  have hμt : μ t ≠ 0 := fun h => hμs (measure_mono_null (subset_toMeasurable _ _) h)
  have hSatMeas : MeasurableSet (orbitSaturation (G := G) t) := by
    exact MeasurableSet.iUnion (fun g => htm.preimage (hνns g).measurable)
  have hνSat : ν (orbitSaturation (G := G) t) = 0 := by
    apply measure_iUnion_null
    intro g
    exact (hνns g).preimage_null hνt
  have hμSat : μ (orbitSaturation (G := G) t) ≠ 0 := by
    intro h
    exact hμt (measure_mono_null (subset_orbitSaturation t) h)
  have hμSatc : μ (orbitSaturation (G := G) t)ᶜ = 0 :=
    (hμerg _ hSatMeas (preimage_orbitSaturation t)).resolve_left hμSat
  exact ⟨(orbitSaturation (G := G) t)ᶜ, hSatMeas.compl, hμSatc, by simpa using hνSat⟩
