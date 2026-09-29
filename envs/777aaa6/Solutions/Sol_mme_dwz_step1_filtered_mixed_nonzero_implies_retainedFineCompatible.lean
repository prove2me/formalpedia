-- Prove2me | solution 1 for mme_dwz_step1_filtered_mixed_nonzero_implies_retainedFineCompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T10:45:26.803661+00:00
-- url     : https://prove2.me/submissions/44f9f3a9-39a8-4176-a3ed-d1e5ef445c61

import Definitions.Def_mme_dwz_step1_mixed_fine_callback_predicates
import Theorems.Thm_mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
import Definitions.Def_mme_dwz_step1_projector_basis_api
import Theorems.Thm_mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    Step1FilteredMixedFineCompatibilityProperty
      K m reindex q edge competitor owner W := by
  unfold Step1FilteredMixedFineCompatibilityProperty
  intro hSameZ hSelectedSupport hUseful hNonzero
  unfold Step1FilteredMixedSingletonNonzero at hNonzero
  have hXWitness : ∃ x : AddressModeWord
      (sourceWord reindex edge competitor) 0,
      addressXWordPassesStep1 m (sourceWord reindex edge competitor) x ∧
      PiTensorProduct.map
          (step1FilteredMixedSelectedXMaps K m reindex q edge
            competitor owner W x)
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t ≠ 0 := by
    classical
    let outer := sourceWord reindex edge competitor
    let js := step1MixedOwnerIndex competitor owner
    let T := (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
    let B := fun j ↦ commonStateBrokenAddressObj K m reindex q edge j
    let pre := step1MixedCoarseProj K reindex edge competitor owner
    let maps := step1FilteredMixedSingletonMaps K m reindex q edge
      competitor owner W
    by_contra hExists
    apply hNonzero
    apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
      (K := K) (d := 3) (S := T)
      (U := { V := fun i ↦ (B (js i)).V i, t := 0 })
      0 (coarseAddressModeBasis K outer 0)
      (addressXWordPassesStep1 m outer) (pre 0)
      (((brokenAddressGrading K m outer
        (commonStateBrokenCopy m reindex q edge competitor)).blockProj 0 0).comp
          (addressXStep1Projector K m outer)) maps
    · rfl
    · intro x hx
      change (brokenAddressGrading K m outer
        (commonStateBrokenCopy m reindex q edge competitor)).blockProj 0 0
          (addressXStep1Projector K m outer
            (coarseAddressModeBasis K outer 0 x)) = 0
      rw [addressXStep1Projector_apply_basis_of_not_passes m outer x hx]
      exact LinearMap.map_zero _
    · intro x hx
      dsimp only
      by_contra hSelectedZero
      exact hExists ⟨x, hx, hSelectedZero⟩
  obtain ⟨x, hx, hXNonzero⟩ := hXWitness
  have hYWitness : ∃ y : AddressModeWord
      (sourceWord reindex edge competitor) 1,
      addressYWordPassesStep1 m (sourceWord reindex edge competitor) y ∧
      PiTensorProduct.map
          (step1FilteredMixedSelectedXYMaps K m reindex q edge
            competitor owner W x y)
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t ≠ 0 := by
    classical
    let outer := sourceWord reindex edge competitor
    let js := step1MixedOwnerIndex competitor owner
    let T := (TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L
    let B := fun j ↦ commonStateBrokenAddressObj K m reindex q edge j
    let pre := step1MixedCoarseProj K reindex edge competitor owner
    let maps := step1FilteredMixedSelectedXMaps K m reindex q edge
      competitor owner W x
    by_contra hExists
    apply hXNonzero
    apply mme_piTensorProduct_map_eq_zero_of_selected_basis_singletons_at_mode
      (K := K) (d := 3) (S := T)
      (U := { V := fun i ↦ (B (js i)).V i, t := 0 })
      1 (coarseAddressModeBasis K outer 1)
      (addressYWordPassesStep1 m outer) (pre 1)
      (((brokenAddressGrading K m outer
        (commonStateBrokenCopy m reindex q edge competitor)).blockProj 1 0).comp
          (addressYStep1Projector K m outer)) maps
    · rfl
    · intro y hy
      change (brokenAddressGrading K m outer
        (commonStateBrokenCopy m reindex q edge competitor)).blockProj 1 0
          (addressYStep1Projector K m outer
            (coarseAddressModeBasis K outer 1 y)) = 0
      rw [addressYStep1Projector_apply_basis_of_not_passes m outer y hy]
      exact LinearMap.map_zero _
    · intro y hy
      dsimp only
      by_contra hSelectedZero
      exact hExists ⟨y, hy, hSelectedZero⟩
  obtain ⟨y, hy, hXYNonzero⟩ := hYWitness
  have hFineSupport := hSelectedSupport x hx y hy hXYNonzero
  have hWordFine :=
    mme_dwz_step1_address_words_supported_imply_retainedFineCompatible_fin_copy
      (K := K) (n := n) (N := L)
      m (sourceWord reindex edge) owner competitor hSameZ
      x y W hx hy hUseful hFineSupport
  simpa only [Step1MixedRetainedFineCompatible,
    addressUsefulBlock, addressFineZ] using hWordFine
