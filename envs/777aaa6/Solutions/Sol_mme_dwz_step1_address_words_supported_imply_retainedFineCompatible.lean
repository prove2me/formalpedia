-- Prove2me | solution 1 for mme_dwz_step1_address_words_supported_imply_retainedFineCompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:45:31.396475+00:00
-- url     : https://prove2.me/submissions/9e9db94f-ab09-49f4-9d0b-a84370e66ede

import Definitions.Def_mme_dwz_step1_source_address_filters
import Theorems.Thm_mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
import Theorems.Thm_mme_dwz_table2_completed_fine_words_total_z_histogram
import Definitions.Def_mme_dwz_retained_fine_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MME.DWZSourceAligned

theorem solution
    {K : Type u} [Field K]
    (m : ℕ) {Copy : Type u} {N : ℕ}
    (outer : Copy → Fin N → Fin 15)
    (owner competitor : Copy)
    (hCommonZ : ∀ t,
      DWZSquare.shapeZ (outer owner t) =
        DWZSquare.shapeZ (outer competitor t))
    (xWord : AddressModeWord (outer competitor) 0)
    (yWord : AddressModeWord (outer competitor) 1)
    (zWord : AddressZWord (outer owner))
    (hX : addressXWordPassesStep1 m (outer competitor) xWord)
    (hY : addressYWordPassesStep1 m (outer competitor) yWord)
    (hUseful : addressWordUseful m (outer owner) zWord)
    (hSupported : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ fineSplitGrade
          (![addressModeLeftGrade xWord t,
            addressModeLeftGrade yWord t,
            (zWord t).leftGrade] i)
          (![addressModeRightGrade xWord t,
            addressModeRightGrade yWord t,
            (zWord t).rightGrade] i)) ≠ 0) :
    retainedFineCompatible m outer
      (fun t ↦ fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade)
      competitor := by
  let left : Fin 3 → Fin N → Fin 3 := fun i t ↦
    ![addressModeLeftGrade xWord t,
      addressModeLeftGrade yWord t,
      (zWord t).leftGrade] i
  let right : Fin 3 → Fin N → Fin 3 := fun i t ↦
    ![addressModeRightGrade xWord t,
      addressModeRightGrade yWord t,
      (zWord t).rightGrade] i
  have hCoarse : ∀ i t,
      (left i t).val + (right i t).val =
        (![DWZSquare.shapeX (outer competitor t),
          DWZSquare.shapeY (outer competitor t),
          DWZSquare.shapeZ (outer competitor t)] i).val := by
    intro i t
    fin_cases i
    · simpa only [left, right, Matrix.cons_val_zero,
        addressModeLeftGrade, addressModeRightGrade,
        DWZComponentRestriction.LiftedCoarsePair.leftGrade,
        DWZComponentRestriction.LiftedCoarsePair.rightGrade,
        cwSquarePairGrade] using
        congrArg Fin.val (xWord t).down.2
    · simpa only [left, right, Matrix.cons_val_one, Matrix.cons_val_zero,
        addressModeLeftGrade, addressModeRightGrade,
        DWZComponentRestriction.LiftedCoarsePair.leftGrade,
        DWZComponentRestriction.LiftedCoarsePair.rightGrade,
        cwSquarePairGrade] using
        congrArg Fin.val (yWord t).down.2
    · have hz := congrArg Fin.val (zWord t).down.2
      simpa only [left, right, Matrix.cons_val_two,
        DWZComponentRestriction.LiftedCoarsePair.leftGrade,
        DWZComponentRestriction.LiftedCoarsePair.rightGrade,
        cwSquarePairGrade, hCommonZ t] using hz
  have hFineSupport : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ fineSplitGrade (left i t) (right i t)) ≠ 0 := by
    intro t
    exact hSupported t
  have hTotalOwner : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card
          (TotalZFiber (outer owner)
            (fun t ↦ (zWord t).leftGrade) k a) =
        table2TotalZSplit k a * m := by
    let small : MME.DWZTable2StandardForm.UsefulBlock m (outer owner) :=
      addressUsefulBlock m (outer owner) zWord hUseful
    intro k a
    have h := mme_dwz_table2_completed_fine_words_total_z_histogram
      m (outer owner) small k a
    change Fintype.card
        (TotalZFiber (outer owner) (fun t ↦ (small.1 t).1) k a) =
      table2TotalZSplit k a * m at h
    simpa only [small, addressUsefulBlock, addressFineZ] using h
  have hTotal : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber (outer competitor) (left 2) k a) =
        table2TotalZSplit k a * m := by
    intro k a
    let e : TotalZFiber (outer competitor) (left 2) k a ≃
        TotalZFiber (outer owner) (fun t ↦ (zWord t).leftGrade) k a :=
      { toFun := fun t ↦ ⟨t.1,
          ⟨(hCommonZ t.1).trans t.2.1, by simpa only [left,
            Matrix.cons_val_two] using t.2.2⟩⟩
        invFun := fun t ↦ ⟨t.1,
          ⟨(hCommonZ t.1).symm.trans t.2.1, by simpa only [left,
            Matrix.cons_val_two] using t.2.2⟩⟩
        left_inv := fun t ↦ by cases t; rfl
        right_inv := fun t ↦ by cases t; rfl }
    rw [Fintype.card_congr e]
    exact hTotalOwner k a
  have hCompat :=
    mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
      (K := K) 6 m (outer competitor) left right hCoarse hFineSupport hX hY
        hTotal
  simpa only [retainedFineCompatible, left, Matrix.cons_val_two,
    fineSplitLeft_encode] using hCompat
