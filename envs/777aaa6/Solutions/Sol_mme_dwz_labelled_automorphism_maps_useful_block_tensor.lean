-- Prove2me | solution 1 for mme_dwz_labelled_automorphism_maps_useful_block_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:16:36.003547+00:00
-- url     : https://prove2.me/submissions/1f25ab8e-b2b3-41b6-ab46-1bb1e9ea4588

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Mathlib.Tactic.FinCases

open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (m : ℕ)
    (D : DWZStandardLabelledData K m)
    (move : Equiv.Perm (DWZStandardBlock m))
    (F : ∀ i : Fin 3, D.X.V i ≃ₗ[K] D.X.V i)
    (hFtensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) D.X.t = D.X.t)
    (hFbasis : ∀ W : GroupedAllowedWords.{u} m,
      ∃ W' : GroupedAllowedWords.{u} m,
        F 2 (D.basis W) = D.basis W' ∧
          D.label W' = move (D.label W))
    (block : DWZStandardBlock m) :
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (dwzLabelledUsefulBlockTensor K m D block) =
      dwzLabelledUsefulBlockTensor K m D (move block) := by
  unfold dwzLabelledUsefulBlockTensor
  let before := Function.update (fun _ ↦ LinearMap.id) 2
    (basisLabelProjection D.basis D.label {block})
  let after := Function.update (fun _ ↦ LinearMap.id) 2
    (basisLabelProjection D.basis D.label {move block})
  have hZ :
      (F 2).toLinearMap.comp
          (basisLabelProjection D.basis D.label {block}) =
        (basisLabelProjection D.basis D.label {move block}).comp
          (F 2).toLinearMap := by
    apply D.basis.ext
    intro W
    obtain ⟨W', hFW, hlabel⟩ := hFbasis W
    have hFW' : (F 2).toLinearMap (D.basis W) = D.basis W' := hFW
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    unfold basisLabelProjection
    rw [Module.Basis.constr_basis]
    simp only [Finset.mem_singleton]
    by_cases hW : D.label W = block
    · rw [if_pos hW]
      rw [hFW', Module.Basis.constr_basis]
      have hW' : D.label W' = move block :=
        hlabel.trans (congrArg move hW)
      rw [if_pos hW']
    · rw [if_neg hW, map_zero]
      rw [hFW', Module.Basis.constr_basis]
      rw [if_neg]
      intro hW'
      apply hW
      apply move.injective
      exact hlabel.symm.trans hW'
  have hfamily :
      (fun i ↦ (F i).toLinearMap.comp (before i)) =
        (fun i ↦ (after i).comp (F i).toLinearMap) := by
    funext i
    fin_cases i
    · ext x
      rfl
    · ext x
      rfl
    · simpa [before, after] using hZ
  change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (PiTensorProduct.map before D.X.t) =
    PiTensorProduct.map after D.X.t
  calc
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (PiTensorProduct.map before D.X.t) =
        PiTensorProduct.map
          (fun i ↦ (F i).toLinearMap.comp (before i)) D.X.t := by
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    _ = PiTensorProduct.map
          (fun i ↦ (after i).comp (F i).toLinearMap) D.X.t := by
      rw [hfamily]
    _ = PiTensorProduct.map after
          (PiTensorProduct.map (fun i ↦ (F i).toLinearMap) D.X.t) := by
      rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    _ = PiTensorProduct.map after D.X.t := by rw [hFtensor]
