-- Prove2me | solution 1 for mme_dwz_labelled_broken_shuffle_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:25:25.688963+00:00
-- url     : https://prove2.me/submissions/9a51d2fd-b33d-48c0-8e63-7a543f0f4127

import Theorems.Thm_mme_dwz_labelled_broken_inclusion_eq_nonhole_sum
import Theorems.Thm_mme_dwz_labelled_automorphism_maps_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m)
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (F : ∀ i : Fin 3, D.X.V i ≃ₗ[K] D.X.V i)
    (hFtensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) D.X.t = D.X.t)
    (hFbasis : ∀ W : GroupedAllowedWords.{u} m,
      ∃ W' : GroupedAllowedWords.{u} m,
        F 2 (D.basis W) = D.basis W' ∧
          D.label W' = move (D.label W)) :
    let G := D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ copy.nonholes)
    ∃ shuffleMap : ∀ i,
        (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      PiTensorProduct.map shuffleMap (G.blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzLabelledUsefulBlockTensor K m D block
          else 0 := by
  classical
  dsimp only
  let G := D.X.basisZAllowedGrading D.basis
    (fun W ↦ D.label W ∈ copy.nonholes)
  let inclusion : ∀ i,
      (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i := fun i ↦
    (G.classOf i 0).subtype
  let shuffleMap : ∀ i,
      (G.blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i := fun i ↦
    (F i).toLinearMap.comp (inclusion i)
  refine ⟨shuffleMap, ?_⟩
  change PiTensorProduct.map
      (fun i ↦ (F i).toLinearMap.comp (inclusion i))
        (G.blockSubtensor (fun _ ↦ 0)).t = _
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
    (PiTensorProduct.map (fun i ↦ (G.classOf i 0).subtype)
      (G.blockSubtensor (fun _ ↦ 0)).t) = _
  rw [mme_dwz_labelled_broken_inclusion_eq_nonhole_sum, map_sum]
  have hFblock : ∀ block : DWZStandardBlock m,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (dwzLabelledUsefulBlockTensor K m D block) =
        dwzLabelledUsefulBlockTensor K m D (move block) := by
    intro block
    exact mme_dwz_labelled_automorphism_maps_useful_block_tensor
      K m D move F hFtensor hFbasis block
  simp_rw [hFblock]
  rw [← Equiv.sum_comp move]
  simp only [Equiv.symm_apply_apply]
  symm
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const_zero, add_zero]
