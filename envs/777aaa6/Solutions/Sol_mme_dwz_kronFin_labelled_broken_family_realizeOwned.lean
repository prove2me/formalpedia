-- Prove2me | solution 1 for mme_dwz_kronFin_labelled_broken_family_realizeOwned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:07:41.27833+00:00
-- url     : https://prove2.me/submissions/9bbc0ba0-40c2-4883-afd5-37589c0eb623

import Theorems.Thm_mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
import Theorems.Thm_mme_dwz_labelled_broken_owner_projection_realizes_exact_sum

open BigOperators Finset
open MME Module PiTensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

theorem solution
    (K : Type u) [Field K] (m : ℕ) {s : ℕ}
    (copies : Fin s →
      MME.DWZSquare.BrokenBlockCopy (DWZStandardBlock m)) :
    let D : DWZStandardLabelledData K m :=
      { X := TensorObj.kronFin 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m)
        basis := TensorObj.kronFinModePiBasis 15
          (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
          (fun r ↦ restrictedComponentZBasis K r m)
        label := groupedUsefulBlock m }
    let G : Fin s → D.X.TypeGrading 2 := fun t ↦
      D.X.basisZAllowedGrading D.basis
        (fun W ↦ D.label W ∈ (copies t).nonholes)
    let Shuffle :=
      MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
        (groupedOuter (m := m))
    ∃ shuffleMap : (Fin s → Shuffle) →
        ∀ t i,
          ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
      ∀ (shuffles : Fin s → Shuffle)
          (owner : DWZStandardBlock m → Fin s),
        (∀ block : DWZStandardBlock m,
          (MulAction.toPerm (shuffles (owner block))).symm block ∈
            (copies (owner block)).nonholes) →
        ∃ f : ∀ t i,
            ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
          (∀ t, f t 0 = shuffleMap shuffles t 0) ∧
          (∀ t, f t 1 = shuffleMap shuffles t 1) ∧
          ∀ t,
            PiTensorProduct.map (f t)
                ((G t).blockSubtensor (fun _ ↦ 0)).t =
              ∑ block : DWZStandardBlock m,
                if t = owner block then
                  dwzLabelledUsefulBlockTensor K m D block
                else 0 := by
  classical
  dsimp only
  let D : DWZStandardLabelledData K m :=
    { X := TensorObj.kronFin 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m)
      basis := TensorObj.kronFinModePiBasis 15
        (fun r : Fin 15 ↦ restrictedComponentPower K r m) 2
        (fun r ↦ restrictedComponentZBasis K r m)
      label := groupedUsefulBlock m }
  let G : Fin s → D.X.TypeGrading 2 := fun t ↦
    D.X.basisZAllowedGrading D.basis
      (fun W ↦ D.label W ∈ (copies t).nonholes)
  let baseMap : ∀ (t : Fin s)
      (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
        (groupedOuter (m := m))),
      ∀ i,
        ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i := fun t g ↦
    Classical.choose
      (mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
        K m (copies t) g)
  have hbaseMap : ∀ (t : Fin s)
      (g : MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
        (groupedOuter (m := m))),
      PiTensorProduct.map (baseMap t g)
          ((G t).blockSubtensor (fun _ ↦ 0)).t =
        ∑ block : DWZStandardBlock m,
          if (MulAction.toPerm g).symm block ∈ (copies t).nonholes then
            dwzLabelledUsefulBlockTensor K m D block
          else 0 := by
    intro t g
    exact Classical.choose_spec
      (mme_dwz_kronFin_labelled_broken_grouped_shuffle_expansion
        K m (copies t) g)
  let shuffleMap := fun
      (shuffles : Fin s →
        MME.DWZTable2StandardForm.UsefulBlockShuffleGroup
          (groupedOuter (m := m)))
      (t : Fin s) (i : Fin 3) ↦ baseMap t (shuffles t) i
  refine ⟨shuffleMap, ?_⟩
  intro shuffles owner howner
  have hcopy : ∀ t : Fin s,
      ∃ f : ∀ i,
          ((G t).blockSubtensor (fun _ ↦ 0)).V i →ₗ[K] D.X.V i,
        f 0 = shuffleMap shuffles t 0 ∧
        f 1 = shuffleMap shuffles t 1 ∧
        PiTensorProduct.map f
            ((G t).blockSubtensor (fun _ ↦ 0)).t =
          ∑ block : DWZStandardBlock m,
            if t = owner block then
              dwzLabelledUsefulBlockTensor K m D block
            else 0 := by
    intro t
    apply mme_dwz_labelled_broken_owner_projection_realizes_exact_sum
      K m D (copies t) (MulAction.toPerm (shuffles t)) owner t
      (baseMap t (shuffles t))
    · exact hbaseMap t (shuffles t)
    · intro block ht
      simpa [ht] using howner block
  choose f hf0 hf1 hftensor using hcopy
  refine ⟨f, ?_, ?_, hftensor⟩
  · intro t
    exact hf0 t
  · intro t
    exact hf1 t
