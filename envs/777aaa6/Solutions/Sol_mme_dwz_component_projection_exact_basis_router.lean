-- Prove2me | solution 1 for mme_dwz_component_projection_exact_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T21:22:11.656129+00:00
-- url     : https://prove2.me/submissions/bda87f84-c999-43e3-8b6e-58556f8f638e

import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZComponentRestriction

noncomputable def componentProjectionMapForRouter
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) (i : Fin 3) :
    (((canonicalComponentBlock K s).kronPow
      (DWZTable2Counts.component s * m)).V i) →ₗ[K]
      ((restrictedComponentPower K s m).V i) :=
  (componentPowerProjectionGrading K s m).blockProj i 0

private theorem componentProjectionMapForRouter_preserves_tensor
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) :
    PiTensorProduct.map (componentProjectionMapForRouter K s m)
        ((canonicalComponentBlock K s).kronPow
          (DWZTable2Counts.component s * m)).t =
      (restrictedComponentPower K s m).t := by
  rfl

private theorem componentPowerZBasis_mem_allowed_forRouter
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (w : PowIndex
      (LiftedCoarsePair.{u} 6 (DWZSquare.shapeZ s))
      (DWZTable2Counts.component s * m))
    (hw : componentWordAllowed s m w) :
    componentPowerZBasis K s m w ∈
      (componentPowerProjectionGrading K s m).classOf 2 0 := by
  classical
  unfold componentPowerProjectionGrading TensorObj.basisZAllowedGrading
  change componentPowerZBasis K s m w ∈
    cwBasisGrade (componentPowerZBasis K s m)
      (fun j ↦ if componentWordAllowed s m j then 0 else 1) 0
  unfold cwBasisGrade
  apply Submodule.subset_span
  refine ⟨w, ?_, rfl⟩
  change (if componentWordAllowed s m w then (0 : Fin 2) else 1) = 0
  rw [if_pos hw]

private theorem componentPowerZBasis_mem_disallowed_forRouter
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (w : PowIndex
      (LiftedCoarsePair.{u} 6 (DWZSquare.shapeZ s))
      (DWZTable2Counts.component s * m))
    (hw : ¬ componentWordAllowed s m w) :
    componentPowerZBasis K s m w ∈
      (componentPowerProjectionGrading K s m).classOf 2 1 := by
  classical
  unfold componentPowerProjectionGrading TensorObj.basisZAllowedGrading
  change componentPowerZBasis K s m w ∈
    cwBasisGrade (componentPowerZBasis K s m)
      (fun j ↦ if componentWordAllowed s m j then 0 else 1) 1
  unfold cwBasisGrade
  apply Submodule.subset_span
  refine ⟨w, ?_, rfl⟩
  change (if componentWordAllowed s m w then (0 : Fin 2) else 1) = 1
  rw [if_neg hw]

private theorem restrictedComponentZBasis_coe_forRouter
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (W : AvailableComponentWord.{u} s m) :
    (restrictedComponentZBasis K s m W).1 =
      componentPowerZBasis K s m W.1 := by
  let b := componentPowerZBasis K s m
  let v : AvailableComponentWord.{u} s m →
      (((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m)).V 2) :=
    fun w ↦ b w.1
  have hv : LinearIndependent K v := by
    exact b.linearIndependent.comp
      (fun w : AvailableComponentWord.{u} s m ↦ w.1)
      Subtype.val_injective
  have hrange : Set.range v =
      b '' {w | componentWordAllowed s m w} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) =
      (componentPowerProjectionGrading K s m).classOf 2 0 := by
    rw [hrange]
    symm
    exact (mme_dwz_table2_component_projection_certificate
      (K := K) s m).2.2.2
  change ↑(((Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)) W) = b W.1
  rw [Module.Basis.map_apply]
  change ↑((Basis.span hv) W) = b W.1
  rw [Module.Basis.span_apply]

private theorem componentProjectionMapForRouter_allowed_basis
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (w : PowIndex
      (LiftedCoarsePair.{u} 6 (DWZSquare.shapeZ s))
      (DWZTable2Counts.component s * m))
    (hw : componentWordAllowed s m w) :
    componentProjectionMapForRouter K s m 2
        (componentPowerZBasis K s m w) =
      restrictedComponentZBasis K s m ⟨w, hw⟩ := by
  apply Subtype.ext
  change (((componentPowerProjectionGrading K s m).blockProj 2 0
      (componentPowerZBasis K s m w)) :
        ((canonicalComponentBlock K s).kronPow
          (DWZTable2Counts.component s * m)).V 2) = _
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _
    (componentPowerZBasis_mem_allowed_forRouter s m w hw)]
  exact (restrictedComponentZBasis_coe_forRouter
    (K := K) s m ⟨w, hw⟩).symm

private theorem componentProjectionMapForRouter_disallowed_basis
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ)
    (w : PowIndex
      (LiftedCoarsePair.{u} 6 (DWZSquare.shapeZ s))
      (DWZTable2Counts.component s * m))
    (hw : ¬ componentWordAllowed s m w) :
    componentProjectionMapForRouter K s m 2
        (componentPowerZBasis K s m w) = 0 := by
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (componentPowerProjectionGrading K s m) 2 0 1 (by decide)
      (componentPowerZBasis K s m w)
      (componentPowerZBasis_mem_disallowed_forRouter s m w hw)

end MME.DWZComponentRestriction

theorem solution
    {K : Type u} [Field K] (s : Fin 15) (m : ℕ) :
    ∃ f : ∀ i : Fin 3,
        (((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
          (MME.DWZTable2Counts.component s * m)).V i) →ₗ[K]
          ((MME.DWZComponentRestriction.restrictedComponentPower K s m).V i),
      PiTensorProduct.map f
          ((MME.DWZComponentRestriction.canonicalComponentBlock K s).kronPow
            (MME.DWZTable2Counts.component s * m)).t =
        (MME.DWZComponentRestriction.restrictedComponentPower K s m).t ∧
      (∀ (w : MME.DWZComponentRestriction.PowIndex
          (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
            (MME.DWZSquare.shapeZ s))
          (MME.DWZTable2Counts.component s * m))
          (hw : MME.DWZComponentRestriction.componentWordAllowed s m w),
        f 2 (MME.DWZComponentRestriction.componentPowerZBasis K s m w) =
          MME.DWZComponentRestriction.restrictedComponentZBasis K s m
            ⟨w, hw⟩) ∧
      ∀ (w : MME.DWZComponentRestriction.PowIndex
          (MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6
            (MME.DWZSquare.shapeZ s))
          (MME.DWZTable2Counts.component s * m)),
        ¬ MME.DWZComponentRestriction.componentWordAllowed s m w →
          f 2 (MME.DWZComponentRestriction.componentPowerZBasis K s m w) = 0 := by
  refine ⟨MME.DWZComponentRestriction.componentProjectionMapForRouter K s m,
    ?_, ?_, ?_⟩
  · exact MME.DWZComponentRestriction.componentProjectionMapForRouter_preserves_tensor
      K s m
  · intro w hw
    exact MME.DWZComponentRestriction.componentProjectionMapForRouter_allowed_basis
      s m w hw
  · intro w hw
    exact MME.DWZComponentRestriction.componentProjectionMapForRouter_disallowed_basis
      s m w hw
