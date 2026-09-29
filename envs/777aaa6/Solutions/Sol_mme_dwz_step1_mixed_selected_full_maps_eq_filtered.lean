-- Prove2me | solution 1 for mme_dwz_step1_mixed_selected_full_maps_eq_filtered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:46:11.611851+00:00
-- url     : https://prove2.me/submissions/1bdb7ec8-2282-441e-9f8f-3e354d6eef75

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
import Theorems.Thm_mme_basisLabelProjection_comp_equiv_of_maps_basis
import Theorems.Thm_mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

private theorem coarseAddressModeBasis_two_eq_Z_private
    {K : Type u} [Field K] {N : ℕ} (outer : Fin N → Fin 15) :
    coarseAddressModeBasis K outer 2 = coarseAddressZBasis K outer := by
  rfl

private theorem filtered_mode_zero
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y 0 =
      step1MixedSelectedNormalMap K m reindex q edge
        competitor owner W x y 0 := by
  unfold step1FilteredMixedSelectedXYMaps
  rw [Function.update_of_ne (by decide)]
  unfold step1FilteredMixedSelectedXMaps
  rw [Function.update_self]
  unfold step1MixedSelectedNormalMap step1MixedSelectedWord
  unfold step1FilteredBrokenAddressMaps addressStep1Projector
  rfl

private theorem filtered_mode_one
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y 1 =
      step1MixedSelectedNormalMap K m reindex q edge
        competitor owner W x y 1 := by
  unfold step1FilteredMixedSelectedXYMaps
  rw [Function.update_self]
  unfold step1MixedSelectedNormalMap step1MixedSelectedWord
  unfold step1FilteredBrokenAddressMaps addressStep1Projector
  rfl

private theorem filtered_mode_two
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y 2 =
      step1MixedSelectedNormalMap K m reindex q edge
        competitor owner W x y 2 := by
  unfold step1FilteredMixedSelectedXYMaps
  rw [Function.update_of_ne (by decide)]
  unfold step1FilteredMixedSelectedXMaps
  rw [Function.update_of_ne (by decide)]
  unfold step1FilteredMixedSingletonMaps
  unfold step1FilteredMixedSingletonAddressPost
  rw [Function.update_self]
  unfold step1MixedSelectedNormalMap
  unfold step1FilteredBrokenAddressMaps
  simp [step1MixedOwnerIndex]
  have hprojector :
      addressStep1Projector K m (sourceWord reindex edge owner) 2 =
        LinearMap.id := by
    rfl
  have hselected :
      step1MixedSelectedWord reindex edge competitor owner W x y 2 = W := by
    rfl
  rw [hprojector, hselected, coarseAddressModeBasis_two_eq_Z_private]
  apply DFunLike.ext _ _
  intro v
  rfl

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    step1MixedSelectedFullMaps K m reindex q edge
        competitor owner W x y =
      step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y := by
  have hFullNormal :
      step1MixedSelectedFullMaps K m reindex q edge
          competitor owner W x y =
        step1MixedSelectedNormalMap K m reindex q edge
          competitor owner W x y := by
    funext i
    let base := step1FilteredBrokenAddressMaps K m
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))
      (commonStateBrokenCopy m reindex q edge
        (step1MixedOwnerIndex competitor owner i)) i
    let modeEquiv := step1MixedModeEquiv K reindex edge competitor owner i
    let mixedBasis := arbitraryCoarseAddressModeBasis K
      (step1MixedAddress reindex edge competitor owner) i
    let ownerBasis := coarseAddressModeBasis K
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i)) i
    let selected := step1MixedSelectedWord reindex edge
      competitor owner W x y i
    let mixedSingleton := DWZComponentRestriction.basisLabelProjection
      mixedBasis id {selected}
    let ownerSingleton := DWZComponentRestriction.basisLabelProjection
      ownerBasis id {selected}
    let coarseProj := gradedAddressProj
      (cwSquareCanonicalGrading K 6) L
        (step1MixedAddress reindex edge competitor owner) i
    have hbasis : ∀ a, modeEquiv (mixedBasis a) = ownerBasis a := by
      intro a
      exact mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis
        reindex edge competitor owner i a
    have hproj :
        ownerSingleton.comp modeEquiv.toLinearMap =
          modeEquiv.toLinearMap.comp mixedSingleton :=
      mme_basisLabelProjection_comp_equiv_of_maps_basis
        mixedBasis ownerBasis modeEquiv hbasis selected
    change (((base.comp modeEquiv.toLinearMap).comp mixedSingleton).comp
        coarseProj) =
      ((base.comp ownerSingleton).comp
        (step1MixedCoarseProj K reindex edge competitor owner i))
    apply DFunLike.ext _ _
    intro v
    change base (modeEquiv (mixedSingleton (coarseProj v))) =
      base (ownerSingleton (modeEquiv (coarseProj v)))
    exact congrArg base (LinearMap.congr_fun hproj (coarseProj v)).symm
  have hFilteredNormal :
      step1FilteredMixedSelectedXYMaps K m reindex q edge
          competitor owner W x y =
        step1MixedSelectedNormalMap K m reindex q edge
          competitor owner W x y := by
    funext i
    fin_cases i
    · exact filtered_mode_zero m reindex q edge competitor owner W x y
    · exact filtered_mode_one m reindex q edge competitor owner W x y
    · exact filtered_mode_two m reindex q edge competitor owner W x y
  exact hFullNormal.trans hFilteredNormal.symm
