-- Prove2me | solution 1 for MeasureEquivalenceEquidecomposition.exists_piecewise_measure_transport
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:19:15.859312+00:00
-- url     : https://prove2.me/submissions/bdc889db-b0ff-48fc-bf42-f20e7c6c7a8b

import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Theorems.Thm_MeasureEquivalenceEquidecomposition_restrict_eq_sum_of_disjoint_cover

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

theorem solution
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
      (∀ᵐ x ∂μ.restrict B, F (H x) = x) := by
  have hFagree : Pairwise (fun i j => EqOn (e i) (e j) (C i ∩ C j)) := by
    intro i j hij x hx
    exact (Set.disjoint_left.mp (hCdis hij) hx.1 hx.2).elim
  have hHagree : Pairwise (fun i j => EqOn (e i).symm (e j).symm (T i ∩ T j)) := by
    intro i j hij x hx
    exact (Set.disjoint_left.mp (hTdis hij) hx.1 hx.2).elim
  obtain ⟨F, hFm, hF⟩ := exists_measurable_piecewise C hCm
    (fun n => e n) (fun n => (e n).measurable) hFagree
  obtain ⟨H, hHm, hH⟩ := exists_measurable_piecewise T hTm
    (fun n => (e n).symm) (fun n => (e n).symm.measurable) hHagree
  have hsumA := restrict_eq_sum_of_disjoint_cover μ A C hCm hCsub hCdis hcoverA
  have hsumB := restrict_eq_sum_of_disjoint_cover μ B T hTm hTsub hTdis hcoverB
  have hmapF (n : ℕ) : (μ.restrict (C n)).map F = μ.restrict (T n) := by
    have hFeq : F =ᵐ[μ.restrict (C n)] e n := by
      filter_upwards [ae_restrict_mem (hCm n)] with x hx using hF n hx
    rw [Measure.map_congr hFeq, ← himage]
    exact ((he n).restrict_image_emb (e n).measurableEmbedding (C n)).map_eq
  have hmapH (n : ℕ) : (μ.restrict (T n)).map H = μ.restrict (C n) := by
    have hHeq : H =ᵐ[μ.restrict (T n)] (e n).symm := by
      filter_upwards [ae_restrict_mem (hTm n)] with x hx using hH n hx
    rw [Measure.map_congr hHeq]
    have hsymimage : (e n).symm '' T n = C n := by
      rw [← himage]
      exact (e n).symm_image_image (C n)
    rw [← hsymimage]
    exact ((he n).symm.restrict_image_emb (e n).symm.measurableEmbedding (T n)).map_eq
  have hFMP : MeasurePreserving F (μ.restrict A) (μ.restrict B) := by
    refine ⟨hFm, ?_⟩
    rw [hsumA, Measure.map_sum hFm.aemeasurable]
    simp_rw [hmapF]
    exact hsumB.symm
  have hHMP : MeasurePreserving H (μ.restrict B) (μ.restrict A) := by
    refine ⟨hHm, ?_⟩
    rw [hsumB, Measure.map_sum hHm.aemeasurable]
    simp_rw [hmapH]
    exact hsumA.symm
  refine ⟨F, H, hFMP, hHMP, hF, hH, ?_, ?_⟩
  · rw [hsumA, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hCm n)] with x hx
    have hext : e n x ∈ T n := by rw [← himage]; exact mem_image_of_mem _ hx
    rw [hF n hx, hH n hext]
    exact (e n).symm_apply_apply x
  · rw [hsumB, Measure.ae_sum_iff]
    intro n
    filter_upwards [ae_restrict_mem (hTm n)] with x hx
    have hext : (e n).symm x ∈ C n := by
      rw [← himage] at hx
      obtain ⟨z, hz, hez⟩ := hx
      simpa only [← hez, MeasurableEquiv.symm_apply_apply] using hz
    rw [hH n hx, hF n hext]
    exact (e n).apply_symm_apply x
