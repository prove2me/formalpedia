-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.finite_permutation_invariant_of_zeroSum_invariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:36:48.962041+00:00
-- url     : https://prove2.me/submissions/ccebcbf0-13b2-48a5-a3d2-b21373b38983

import Definitions.Def_BenchmarkOperator20261026_RationalFiberErgodic
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_aeconst_of_dense_translation_invariant
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_exists_base_event_of_ae_fiber_const
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_finite_exponential_ac_volume
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_measurePreserving_sumTailEquiv

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

-- Preserved source skeleton: RationalFiberErgodic
section
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem finite_real_aeconst_of_rational_invariant (n : ℕ)
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun x : Fin n → ℝ => x + fun i => (q i : ℝ)) ⁻¹' E =ᵐ[volume] E) :
    EventuallyConst E (ae (volume : Measure (Fin n → ℝ))) := by
  let f : (Fin n → ℚ) → (Fin n → ℝ) := fun q i => (q i : ℝ)
  have hd : DenseRange f := DenseRange.piMap (fun _ : Fin n => Rat.denseRange_cast)
  apply aeconst_of_dense_translation_invariant volume (range f) hd E hE
  rintro q ⟨r, rfl⟩
  exact hinv r





end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: FiberEventRepresentative
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem ae_fiber_const_of_rational_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set (α × (Fin n → ℝ))) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun z : α × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' E
        =ᵐ[μ.prod volume] E) :
    ∀ᵐ x ∂μ, EventuallyConst (Prod.mk x ⁻¹' E) (ae volume) := by
  have hh : ∀ q : Fin n → ℚ, ∀ᵐ x ∂μ, ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      E (x, y + fun i => (q i : ℝ)) = E (x, y) := fun q =>
    Measure.ae_ae_of_ae_prod (hinv q)
  have hall : ∀ᵐ x ∂μ, ∀ q : Fin n → ℚ, ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
      E (x, y + fun i => (q i : ℝ)) = E (x, y) := ae_all_iff.mpr hh
  filter_upwards [hall] with x hx
  exact finite_real_aeconst_of_rational_invariant n (Prod.mk x ⁻¹' E)
    (measurable_prodMk_left hE) hx

theorem finite_base_ac_volume (n : ℕ) :
    Measure.pi (fun _ : Fin n => baseMeasure) ≪ (volume : Measure (Fin n → ℝ)) := by
  have he : Measure.pi (fun _ : Fin n => baseMeasure) =
      (Measure.pi (fun _ : Fin n => exponentialMeasure)).restrict
        (univ.pi (fun _ => baseInterval)) :=
    (Measure.restrict_pi_pi (fun _ : Fin n => exponentialMeasure) (fun _ => baseInterval)).symm
  rw [he]
  exact Measure.restrict_le_self.absolutelyContinuous.trans (finite_exponential_ac_volume n)

theorem exists_base_event_of_rational_fiber_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set (α × (Fin n → ℝ))) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin n → ℚ,
      (fun z : α × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' E
        =ᵐ[μ.prod volume] E) :
    ∃ A : Set α, MeasurableSet A ∧ E =ᵐ[μ.prod volume] Prod.fst ⁻¹' A :=
  exists_base_event_of_ae_fiber_const μ volume (Measure.pi (fun _ : Fin n => baseMeasure))
    (finite_base_ac_volume n) E hE (ae_fiber_const_of_rational_invariant μ n E hE hinv)

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: SumFiberCoordinates
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct







theorem measurePreserving_sumFiberEquiv (n : ℕ) {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] :
    MeasurePreserving (sumFiberEquiv n α)
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ)
      (((volume : Measure ℝ).prod μ).prod (volume : Measure (Fin n → ℝ))) := by
  have h₁ := (measurePreserving_sumTailEquiv n).prod (MeasurePreserving.id μ)
  have h₂ := measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure (Fin n → ℝ)) μ
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := μ))
  have h₄ := (measurePreserving_prodAssoc (volume : Measure ℝ) μ
    (volume : Measure (Fin n → ℝ))).symm MeasurableEquiv.prodAssoc
  exact h₄.comp (h₃.comp (h₂.comp h₁))

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: ZeroSumFiberEvent
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem exists_sum_event_of_zeroSum_invariant
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set ((Fin (n + 1) → ℝ) × α)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin (n + 1) → ℚ, (∑ i, q i) = 0 →
      (fun z : (Fin (n + 1) → ℝ) × α => (z.1 + fun i => (q i : ℝ), z.2)) ⁻¹' E
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E) :
    ∃ A : Set (ℝ × α), MeasurableSet A ∧ E =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ]
      (fun z => (∑ i, z.1 i, z.2)) ⁻¹' A := by
  let e := sumFiberEquiv n α
  let F := e.symm ⁻¹' E
  have hF : MeasurableSet F := e.symm.measurable hE
  have hm := measurePreserving_sumFiberEquiv n μ
  have hFinv (q : Fin n → ℚ) :
      (fun z : (ℝ × α) × (Fin n → ℝ) => (z.1, z.2 + fun i => (q i : ℝ))) ⁻¹' F
        =ᵐ[((volume : Measure ℝ).prod μ).prod volume] F := by
    let r : Fin (n + 1) → ℚ := Fin.cons (-∑ i, q i) q
    have hr : (∑ i, r i) = 0 := by simp [r, Fin.sum_univ_succ]
    have he (z : (ℝ × α) × (Fin n → ℝ)) :
        (e.symm z).1 + (fun i => (r i : ℝ)) =
          (e.symm (z.1, z.2 + fun i => (q i : ℝ))).1 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, sumFiberEquiv_symm_apply, r, Pi.add_apply, Finset.sum_add_distrib]
        push_cast
        ring
      · simp [e, sumFiberEquiv_symm_apply, r, Pi.add_apply]
    have hh := (hm.symm e).quasiMeasurePreserving.ae (hinv r hr)
    filter_upwards [hh] with z hz
    change E (e.symm (z.1, z.2 + fun i => (q i : ℝ))) = E (e.symm z)
    change E ((e.symm z).1 + (fun i => (r i : ℝ)), (e.symm z).2) = E (e.symm z) at hz
    rw [he] at hz
    exact hz
  obtain ⟨A, hA, hFA⟩ := exists_base_event_of_rational_fiber_invariant
    ((volume : Measure ℝ).prod μ) n F hF hFinv
  refine ⟨A, hA, ?_⟩
  have hh := hm.quasiMeasurePreserving.ae_eq hFA
  filter_upwards [hh] with z hz
  change E (e.symm (e z)) = A (e z).1 at hz
  rw [e.symm_apply_apply] at hz
  exact hz



end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] (n : ℕ)
    (E : Set ((Fin (n + 1) → ℝ) × α)) (hE : MeasurableSet E)
    (hinv : ∀ q : Fin (n + 1) → ℚ, (∑ i, q i) = 0 →
      (fun z : (Fin (n + 1) → ℝ) × α => (z.1 + fun i => (q i : ℝ), z.2)) ⁻¹' E
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E)
    (p : Equiv.Perm (Fin (n + 1))) :
    (fun z : (Fin (n + 1) → ℝ) × α => (fun i => z.1 (p i), z.2)) ⁻¹' E
      =ᵐ[(volume : Measure (Fin (n + 1) → ℝ)).prod μ] E := by
  obtain ⟨A, hA, he⟩ := exists_sum_event_of_zeroSum_invariant μ n E hE hinv
  have hp : MeasurePreserving
      (fun z : (Fin (n + 1) → ℝ) × α => (fun i => z.1 (p i), z.2))
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ)
      ((volume : Measure (Fin (n + 1) → ℝ)).prod μ) := by
    convert (volume_measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => ℝ) p.symm).prod
        (MeasurePreserving.id μ) using 1
    funext z
    apply Prod.ext
    · funext i
      simp [Prod.map, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    · rfl
  have hh := hp.quasiMeasurePreserving.ae_eq he
  filter_upwards [hh, he] with z hz hz'
  change E (fun i => z.1 (p i), z.2) = A (∑ i, z.1 (p i), z.2) at hz
  change E z = A (∑ i, z.1 i, z.2) at hz'
  change E (fun i => z.1 (p i), z.2) = E z
  rw [hz, hz']
  congr 2
  exact Equiv.sum_comp p z.1
