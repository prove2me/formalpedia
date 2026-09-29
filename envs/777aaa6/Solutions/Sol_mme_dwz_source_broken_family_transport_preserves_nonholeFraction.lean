-- Prove2me | solution 1 for mme_dwz_source_broken_family_transport_preserves_nonholeFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:01:30.893118+00:00
-- url     : https://prove2.me/submissions/4dffdb94-4604-4bff-904f-9494799bdadd

import Theorems.Thm_mme_dwz_source_broken_family_transport_to_grouped_standard
import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (S : TensorObj K 3) {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (houter : ∀ j : Fin k, ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer j r = s} =
        DWZTable2Counts.component s * m)
    (hm : 0 < m)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hSource : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦
        DWZSourceAligned.brokenAddressObj K m (outer j) (copy j))) S) :
    ∃ standardCopy : Fin k → DWZSquare.BrokenBlockCopy
        (DWZComponentRestriction.DWZStandardBlock m),
      (∀ j : Fin k,
        DWZSquare.nonholeFraction (standardCopy j) =
          DWZSquare.nonholeFraction (copy j)) ∧
      let D : DWZComponentRestriction.DWZStandardLabelledData K m :=
        { X := TensorObj.kronFin 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m)
          basis := TensorObj.kronFinModePiBasis 15
            (fun r : Fin 15 ↦
              DWZComponentRestriction.restrictedComponentPower K r m) 2
            (fun r ↦
              DWZComponentRestriction.restrictedComponentZBasis K r m)
          label := DWZComponentRestriction.groupedUsefulBlock m }
      let G : Fin k → D.X.TypeGrading 2 := fun j ↦
        D.X.basisZAllowedGrading D.basis
          (fun W ↦ D.label W ∈ (standardCopy j).nonholes)
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦
          (G j).blockSubtensor (fun _ ↦ 0))) S := by
  classical
  obtain ⟨standardCopy, hNumerator, hRestrict⟩ :=
    mme_dwz_source_broken_family_transport_to_grouped_standard
      S outer houter hm copy hSource
  refine ⟨standardCopy, ?_, hRestrict⟩
  intro j
  obtain ⟨positionEquiv, hposition, blockEquiv, hblock, transported,
      htransportedCard, htransportedMem⟩ :=
    mme_dwz_table2_broken_copy_transport_to_standard
      (outer j) (houter j) (copy j)
  have hDenominator :
      Fintype.card (DWZTable2StandardForm.UsefulBlock m (outer j)) =
        Fintype.card (DWZComponentRestriction.DWZStandardBlock m) :=
    Fintype.card_congr blockEquiv
  unfold DWZSquare.nonholeFraction
  rw [hNumerator j, ← hDenominator]
