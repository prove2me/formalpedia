-- Prove2me | solution 1 for mme_dwz_broken_standard_owner_projection_realizes_exact_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:34:58.697206+00:00
-- url     : https://prove2.me/submissions/ef244528-eef3-41f1-8e5c-69b41f39d4b1

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_owner_projection_standard_useful_block_tensor

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (m : ℕ) {s : ℕ}
    (copy : MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m))
    (move : Equiv.Perm (DWZStandardBlock m))
    (owner : DWZStandardBlock m → Fin s) (t : Fin s)
    (shuffleMap : ∀ i,
      (dwzBrokenStandardObj K m copy).V i →ₗ[K]
        (dwzStandardLabelledData K m).X.V i)
    (hshuffle :
      PiTensorProduct.map shuffleMap (dwzBrokenStandardObj K m copy).t =
        ∑ block : DWZStandardBlock m,
          if move.symm block ∈ copy.nonholes then
            dwzStandardUsefulBlockTensor K m block
          else 0)
    (howner : ∀ block : DWZStandardBlock m, t = owner block →
      move.symm block ∈ copy.nonholes) :
    ∃ f : ∀ i,
        (dwzBrokenStandardObj K m copy).V i →ₗ[K]
          (dwzStandardLabelledData K m).X.V i,
      f 0 = shuffleMap 0 ∧
      f 1 = shuffleMap 1 ∧
      PiTensorProduct.map f (dwzBrokenStandardObj K m copy).t =
        ∑ block : DWZStandardBlock m,
          if t = owner block then
            dwzStandardUsefulBlockTensor K m block
          else 0 := by
  classical
  let ownerMaps :=
    Function.update (fun _ ↦ LinearMap.id) 2
      (basisLabelProjection (dwzStandardLabelledData K m).basis
        (dwzStandardLabelledData K m).label
        (Finset.univ.filter (fun b ↦ t = owner b)))
  let f : ∀ i,
      (dwzBrokenStandardObj K m copy).V i →ₗ[K]
        (dwzStandardLabelledData K m).X.V i := fun i ↦
    (ownerMaps i).comp (shuffleMap i)
  refine ⟨f, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · change PiTensorProduct.map
      (fun i ↦ ownerMaps i ∘ₗ shuffleMap i)
        (dwzBrokenStandardObj K m copy).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    change PiTensorProduct.map
      (Function.update (fun _ ↦ LinearMap.id) 2
        (basisLabelProjection (dwzStandardLabelledData K m).basis
          (dwzStandardLabelledData K m).label
          (Finset.univ.filter (fun b ↦ t = owner b))))
      (PiTensorProduct.map shuffleMap (dwzBrokenStandardObj K m copy).t) = _
    rw [hshuffle, map_sum]
    apply Finset.sum_congr rfl
    intro block _
    by_cases hs : move.symm block ∈ copy.nonholes
    · simp only [hs, if_true]
      rw [dwzStandardUsefulBlockTensor]
      exact mme_dwz_owner_projection_standard_useful_block_tensor
        K m (dwzStandardLabelledData K m) owner t block
    · have hnotOwned : t ≠ owner block := fun ho ↦ hs (howner block ho)
      simp only [hs, if_false, map_zero, hnotOwned]
