-- Prove2me | solution 1 for mme_dwz_source_coarse_address_to_restricted_component_family_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:37:11.616956+00:00
-- url     : https://prove2.me/submissions/1efdf73d-cb2c-47a3-9c60-cdf95efc1958

import Definitions.Def_mme_dwz_restricted_component_z_basis
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
import Theorems.Thm_mme_dwz_source_raw_component_words_allowed_iff_useful
import Theorems.Thm_mme_dwz_component_projection_exact_basis_router
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

namespace MME.DWZSourceAligned

private theorem liftedCoarsePair_leftGrade_cast_router
    {c d : Fin 5} (h : c = d)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6 c) :
    (h ▸ x).leftGrade = x.leftGrade := by
  cases h
  rfl

private theorem liftedCoarsePair_rightGrade_cast_router
    {c d : Fin 5} (h : c = d)
    (x : DWZComponentRestriction.LiftedCoarsePair.{u} 6 c) :
    (h ▸ x).rightGrade = x.rightGrade := by
  cases h
  rfl

private theorem rawFineZ_eq_addressFineZ
    {N m : ℕ} {outer : Fin N → Fin 15}
    (e : DWZComponentRestriction.GroupedPosition m ≃ Fin N)
    (he : ∀ p, outer (e p) =
      DWZComponentRestriction.groupedOuter p)
    (W : AddressZWord.{u} outer)
    (raw : ∀ s : Fin 15,
      DWZComponentRestriction.PowIndex
        (DWZComponentRestriction.LiftedCoarsePair.{u} 6
          (DWZSquare.shapeZ s))
        (DWZTable2Counts.component s * m))
    (hraw : ∀ p : DWZComponentRestriction.GroupedPosition m,
      HEq (DWZComponentRestriction.PowIndex.get
          (DWZTable2Counts.component p.1 * m) (raw p.1) p.2)
        (W (e p)))
    (p : DWZComponentRestriction.GroupedPosition m) :
    let letter := DWZComponentRestriction.PowIndex.get
      (DWZTable2Counts.component p.1 * m) (raw p.1) p.2
    (letter.leftGrade, letter.rightGrade) = addressFineZ W (e p) := by
  dsimp only
  have hshape : DWZSquare.shapeZ (outer (e p)) =
      DWZSquare.shapeZ p.1 := congrArg DWZSquare.shapeZ (he p)
  have hcast : HEq (hshape ▸ W (e p)) (W (e p)) :=
    eqRec_heq hshape (W (e p))
  have hletter :
      DWZComponentRestriction.PowIndex.get
          (DWZTable2Counts.component p.1 * m) (raw p.1) p.2 =
        hshape ▸ W (e p) :=
    eq_of_heq ((hraw p).trans hcast.symm)
  rw [hletter]
  apply Prod.ext
  · exact liftedCoarsePair_leftGrade_cast_router hshape (W (e p))
  · exact liftedCoarsePair_rightGrade_cast_router hshape (W (e p))

/-- The exact source-order coarse address maps to the literal fifteen-factor
restricted Table-2 family.  Useful source words map to the corresponding
grouped restricted basis word with exact fine labels, while non-useful words
are killed. -/
theorem sourceCoarseAddress_to_restrictedComponentFamily_basis_router
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) = DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (coarseAddressObj K outer).V i →ₗ[K]
            (TensorObj.kronFin 15 (fun s ↦
              DWZComponentRestriction.restrictedComponentPower K s m)).V i,
        PiTensorProduct.map f (coarseAddressObj K outer).t =
          (TensorObj.kronFin 15 (fun s ↦
            DWZComponentRestriction.restrictedComponentPower K s m)).t ∧
        (∀ (W : AddressZWord.{u} outer)
          (_hW : addressWordUseful m outer W),
          ∃ Wg : DWZComponentRestriction.GroupedAllowedWords.{u} m,
            f 2 (coarseAddressZBasis K outer W) =
              TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  DWZComponentRestriction.restrictedComponentPower K s m) 2
                (fun s ↦
                  DWZComponentRestriction.restrictedComponentZBasis K s m) Wg ∧
            ∀ p, DWZComponentRestriction.groupedFineZ Wg p =
              addressFineZ W (e p)) ∧
        ∀ W : AddressZWord.{u} outer,
          ¬ addressWordUseful m outer W →
            f 2 (coarseAddressZBasis K outer W) = 0 := by
  obtain ⟨e, he, F, hFtensor, hFbasis⟩ :=
    mme_dwz_source_coarse_address_to_raw_component_powers_exact_Z_basis
      (K := K) outer houter hm
  let rawObj : Fin 15 → TensorObj K 3 := fun s ↦
    (DWZComponentRestriction.canonicalComponentBlock K s).kronPow
      (DWZTable2Counts.component s * m)
  let restrictedObj : Fin 15 → TensorObj K 3 := fun s ↦
    DWZComponentRestriction.restrictedComponentPower K s m
  let package := fun s : Fin 15 ↦
    mme_dwz_component_projection_exact_basis_router (K := K) s m
  let g : ∀ s i, (rawObj s).V i →ₗ[K] (restrictedObj s).V i :=
    fun s ↦ Classical.choose (package s)
  have hgTensor : ∀ s,
      PiTensorProduct.map (g s) (rawObj s).t = (restrictedObj s).t :=
    fun s ↦ (Classical.choose_spec (package s)).1
  have hgAllowed : ∀ s w
      (hw : DWZComponentRestriction.componentWordAllowed s m w),
      g s 2 (DWZComponentRestriction.componentPowerZBasis K s m w) =
        DWZComponentRestriction.restrictedComponentZBasis K s m
          ⟨w, hw⟩ :=
    fun s ↦ (Classical.choose_spec (package s)).2.1
  have hgZero : ∀ s w,
      ¬ DWZComponentRestriction.componentWordAllowed s m w →
      g s 2 (DWZComponentRestriction.componentPowerZBasis K s m w) = 0 :=
    fun s ↦ (Classical.choose_spec (package s)).2.2
  let G : ∀ i : Fin 3,
      (TensorObj.kronFin 15 rawObj).V i →ₗ[K]
        (TensorObj.kronFin 15 restrictedObj).V i :=
    TensorObj.kronFinFamilyModeMap 15 rawObj restrictedObj g
  let f : ∀ i : Fin 3, (coarseAddressObj K outer).V i →ₗ[K]
      (TensorObj.kronFin 15 restrictedObj).V i := fun i ↦
    (G i).comp (F i)
  have hGtensor : PiTensorProduct.map G
      (TensorObj.kronFin 15 rawObj).t =
        (TensorObj.kronFin 15 restrictedObj).t :=
    TensorObj.kronFinFamilyModeMap_preserves_tensor
      rawObj restrictedObj g hgTensor
  refine ⟨e, he, f, ?_, ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (G i).comp (F i))
        (coarseAddressObj K outer).t = _
    rw [PiTensorProduct.map_comp]
    change PiTensorProduct.map G
        (PiTensorProduct.map F (coarseAddressObj K outer).t) = _
    rw [hFtensor, hGtensor]
  · intro W hW
    obtain ⟨raw, hraw, hFword⟩ := hFbasis W
    have hall : ∀ s,
        DWZComponentRestriction.componentWordAllowed s m (raw s) :=
      (mme_dwz_source_raw_component_words_allowed_iff_useful
        e he W raw hraw).2 hW
    let Wg : DWZComponentRestriction.GroupedAllowedWords.{u} m :=
      fun s ↦ ⟨raw s, hall s⟩
    refine ⟨Wg, ?_, ?_⟩
    · change G 2 (F 2 (coarseAddressZBasis K outer W)) = _
      rw [hFword]
      exact mme_kronFin_family_mode_map_selected_basis
        rawObj restrictedObj 2
        (fun s ↦ DWZComponentRestriction.componentPowerZBasis K s m)
        (fun s ↦ DWZComponentRestriction.restrictedComponentZBasis K s m)
        g raw Wg (fun s ↦ hgAllowed s (raw s) (hall s))
    · intro p
      change
        (let letter := DWZComponentRestriction.PowIndex.get
          (DWZTable2Counts.component p.1 * m) (raw p.1) p.2
        (letter.leftGrade, letter.rightGrade)) = addressFineZ W (e p)
      exact rawFineZ_eq_addressFineZ e he W raw hraw p
  · intro W hn
    obtain ⟨raw, hraw, hFword⟩ := hFbasis W
    have hnotAll : ¬ ∀ s,
        DWZComponentRestriction.componentWordAllowed s m (raw s) := by
      intro hall
      exact hn ((mme_dwz_source_raw_component_words_allowed_iff_useful
        e he W raw hraw).1 hall)
    obtain ⟨s, hs⟩ := Classical.not_forall.mp hnotAll
    change G 2 (F 2 (coarseAddressZBasis K outer W)) = 0
    rw [hFword]
    exact TensorObj.kronFinFamilyModeMap_basis_eq_zero_of_exists
      rawObj restrictedObj 2
      (fun s ↦ DWZComponentRestriction.componentPowerZBasis K s m)
      g raw ⟨s, hgZero s (raw s) hs⟩

end MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K] {N m : ℕ}
    (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m)
    (hm : 0 < m) :
    ∃ e : MME.DWZComponentRestriction.GroupedPosition m ≃ Fin N,
      (∀ p, outer (e p) =
        MME.DWZComponentRestriction.groupedOuter p) ∧
      ∃ f : ∀ i : Fin 3,
          (MME.DWZSourceAligned.coarseAddressObj K outer).V i →ₗ[K]
            (MME.TensorObj.kronFin 15 (fun s ↦
              MME.DWZComponentRestriction.restrictedComponentPower K s m)).V i,
        PiTensorProduct.map f
            (MME.DWZSourceAligned.coarseAddressObj K outer).t =
          (MME.TensorObj.kronFin 15 (fun s ↦
            MME.DWZComponentRestriction.restrictedComponentPower K s m)).t ∧
        (∀ (W : MME.DWZSourceAligned.AddressZWord.{u} outer)
          (_hW : MME.DWZSourceAligned.addressWordUseful m outer W),
          ∃ Wg : MME.DWZComponentRestriction.GroupedAllowedWords.{u} m,
            f 2 (MME.DWZSourceAligned.coarseAddressZBasis K outer W) =
              MME.TensorObj.kronFinModePiBasis 15
                (fun s ↦
                  MME.DWZComponentRestriction.restrictedComponentPower K s m) 2
                (fun s ↦
                  MME.DWZComponentRestriction.restrictedComponentZBasis K s m) Wg ∧
            ∀ p, MME.DWZComponentRestriction.groupedFineZ Wg p =
              MME.DWZSourceAligned.addressFineZ W (e p)) ∧
        ∀ W : MME.DWZSourceAligned.AddressZWord.{u} outer,
          ¬ MME.DWZSourceAligned.addressWordUseful m outer W →
            f 2 (MME.DWZSourceAligned.coarseAddressZBasis K outer W) = 0 := by
  exact MME.DWZSourceAligned.sourceCoarseAddress_to_restrictedComponentFamily_basis_router
    outer houter hm
