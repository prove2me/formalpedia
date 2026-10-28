-- Prove2me | solution 1 for MeasureEquivalenceTopology.continuous_borel_hom
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:17:31.058674+00:00
-- url     : https://prove2.me/submissions/243dc0ac-ffe8-4475-8bb0-e2b256067673

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Theorems.Thm_MeasureEquivalenceTopology_pettis_nhds_one

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
Pettis category, Borel-homomorphism continuity, and uniqueness of compatible
Polish group topologies. This is a new standalone verification development.
-/
open Filter Set TopologicalSpace
open scoped Topology Pointwise
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
open MeasureEquivalenceTopology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BaireSpace G]

theorem solution [MeasurableSpace G] [BorelSpace G]
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (f : G →* L) (hf : Measurable f) : Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_split_inv hU
  obtain ⟨W, hWV, hWopen, hWone⟩ := mem_nhds_iff.mp hV
  let C : L → Set L := fun y => {z | z / y ∈ W}
  have hCopen (y : L) : IsOpen (C y) :=
    hWopen.preimage (by fun_prop : Continuous (fun z : L => z / y))
  have hCnhds (y : L) : C y ∈ 𝓝 y := (hCopen y).mem_nhds (by simpa [C])
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hCnhds
  have hcover : (⋃ y ∈ S, f ⁻¹' C y) = (Set.univ : Set G) := by
    have hpre := congrArg (fun T : Set L => f ⁻¹' T) hScover
    simpa only [Set.preimage_iUnion, Set.preimage_univ] using hpre
  have hnon : ∃ y ∈ S, ¬ IsMeagre (f ⁻¹' C y) := by
    by_contra h
    push Not at h
    have hmeagre := isMeagre_biUnion hScount h
    rw [hcover] at hmeagre
    exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hmeagre
  obtain ⟨y, _hyS, hy⟩ := hnon
  have hBP : BaireMeasurableSet (f ⁻¹' C y) :=
    (hf (hCopen y).measurableSet).baireMeasurableSet
  apply Filter.mem_of_superset (pettis_nhds_one hBP hy)
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_div.mp hz
  change f (a / b) ∈ U
  have haV : f a / y ∈ V := hWV ha
  have hbV : f b / y ∈ V := hWV hb
  have hh := hVV (f a / y) haV (f b / y) hbV
  simpa only [map_div, div_div_div_cancel_right] using hh
