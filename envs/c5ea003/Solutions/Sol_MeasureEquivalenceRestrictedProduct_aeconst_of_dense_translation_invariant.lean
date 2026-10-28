-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.aeconst_of_dense_translation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:34:08.608284+00:00
-- url     : https://prove2.me/submissions/2f0dbd9a-f92a-455b-963a-f7cd32f741e5

import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_map_add_eq_of_dense_invariant

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

-- Preserved source skeleton: DenseEventErgodic
section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem ae_eq_set_of_restrict_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : μ.restrict s = μ.restrict t) : s =ᵐ[μ] t := by
  have hd {a b : Set α} (ha : MeasurableSet a) (hb : MeasurableSet b)
      (hab : μ.restrict a = μ.restrict b) : μ (a \ b) = 0 := by
    have hx := congrArg (fun ν : Measure α => ν (a \ b)) hab
    dsimp only at hx
    have h₁ : (a \ b) ∩ a = a \ b := inter_eq_left.mpr diff_subset
    have h₀ : (a \ b) ∩ b = ∅ := by ext x; simp
    rw [Measure.restrict_apply (ha.diff hb), h₁,
      Measure.restrict_apply (ha.diff hb), h₀, measure_empty] at hx
    exact hx
  exact ae_eq_set.mpr ⟨hd hs ht he, hd ht hs he.symm⟩

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [PseudoMetrizableSpace G] [SigmaCompactSpace G]



end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [PseudoMetrizableSpace G] [SigmaCompactSpace G]

theorem solution (μ : Measure G)
    [IsLocallyFiniteMeasure μ] [SFinite μ] [μ.IsAddLeftInvariant]
    (D : Set G) (hD : Dense D) (E : Set G) (hE : MeasurableSet E)
    (hinv : ∀ q ∈ D, (fun x => x + q) ⁻¹' E =ᵐ[μ] E) :
    EventuallyConst E (ae μ) := by
  let ν := μ.restrict E
  letI : ν.Regular := by dsimp only [ν]; infer_instance
  have hν (q : G) (hq : q ∈ D) : ν.map (fun x => x + q) = ν := by
    calc
      ν.map (fun x => x + q) = (μ.restrict ((fun x => x + q) ⁻¹' E)).map
          (fun x => x + q) := by
        dsimp only [ν]
        rw [Measure.restrict_congr_set (hinv q hq).symm]
      _ = (μ.map (fun x => x + q)).restrict E :=
        (Measure.restrict_map (by fun_prop) hE).symm
      _ = ν := by rw [map_add_right_eq_self]
  have hall (g : G) : (fun x => x + g) ⁻¹' E =ᵐ[μ] E := by
    apply ae_eq_set_of_restrict_eq μ ((show Measurable (fun x : G => x + g) from by fun_prop) hE) hE
    let e := MeasurableEquiv.addRight g
    apply e.map_measurableEquiv_injective
    change (μ.restrict ((fun x : G => x + g) ⁻¹' E)).map (fun x => x + g) =
      (μ.restrict E).map (fun x => x + g)
    have he := map_add_eq_of_dense_invariant ν D hD hν g
    dsimp only [ν] at he
    rw [← Measure.restrict_map (by fun_prop) hE, map_add_right_eq_self, he]
  apply MeasureTheory.aeconst_of_forall_preimage_vadd_ae_eq G hE.nullMeasurableSet
  intro g
  simpa only [vadd_eq_add, add_comm] using hall g
