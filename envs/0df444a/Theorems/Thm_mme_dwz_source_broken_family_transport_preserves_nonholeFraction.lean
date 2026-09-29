-- Prove2me | Theorems.Thm_mme_dwz_source_broken_family_transport_preserves_nonholeFraction
-- name    : mme_dwz_source_broken_family_transport_preserves_nonholeFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T18:57:51.822401+00:00
-- url     : https://prove2.me/theorems/8a2588fb-d68a-4764-8a1c-3c7d48388d0c
-- title:
--   Exact-profile source regrouping preserves non-hole fractions
-- statement:
--   Fix a family of exact Table-2 outer words and source-aligned broken copies. Assume their direct sum is a restriction of a source tensor. Regroup every owner from its literal source-coordinate order into the canonical fifteen-component standard order. Then there are grouped broken copies with the same direct-sum restriction and, owner by owner, exactly the same normalized non-hole fraction:
--
--   $$
--   \eta_j^{\mathrm{grouped}}=\eta_j^{\mathrm{source}}.
--   $$
--
--   This normalized transport is the interface needed to pass the aggregate survivor mass from the asymmetric hashing argument into the Hole Lemma without changing either its numerator or its block-universe denominator.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definitions 5.5 and 6.3 and the regrouping used before Lemma 5.6 (printed pp. 47-49 and 54-57).

import Theorems.Thm_mme_dwz_source_broken_family_transport_to_grouped_standard
import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard

open MME Module

universe u

set_option autoImplicit false

theorem mme_dwz_source_broken_family_transport_preserves_nonholeFraction
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
  sorry
