-- Prove2me | solution 1 for mme_dwz_source_address_useful_z_supported_implies_step1_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:02:52.784854+00:00
-- url     : https://prove2.me/submissions/1f3b48a3-fb26-4f1b-9f62-d74965a972b3

import Definitions.Def_mme_dwz_step1_source_address_filters
import Theorems.Thm_mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy

open MME MME.DWZStep1Support

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

open MME.DWZSourceAligned

private theorem blockTensor_ne_zero_congr
    {K : Type u} [Field K] {A : TensorObj K 3} {t : ℕ}
    (G : A.TypeGrading t) {rho sigma : Fin 3 → Fin t}
    (h : rho = sigma) :
    G.blockTensor rho ≠ 0 ↔ G.blockTensor sigma ≠ 0 := by
  subst sigma
  rfl

/-- At the literal source-address basis interface, every supported diagonal
term carrying a useful Z word also passes both Step-1 X/Y word filters. -/
theorem solution
    {K : Type u} [Field K] (m : ℕ) {N : ℕ}
    (outer : Fin N → Fin 15)
    (xWord : AddressModeWord outer 0)
    (yWord : AddressModeWord outer 1)
    (zWord : AddressZWord outer)
    (hUseful : addressWordUseful m outer zWord)
    (hSupported : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ ![
          fineSplitGrade
            (addressModeLeftGrade xWord t)
            (addressModeRightGrade xWord t),
          fineSplitGrade
            (addressModeLeftGrade yWord t)
            (addressModeRightGrade yWord t),
          fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade] i) ≠ 0) :
    addressXWordPassesStep1 m outer xWord ∧
      addressYWordPassesStep1 m outer yWord := by
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
        (![DWZSquare.shapeX (outer t),
          DWZSquare.shapeY (outer t),
          DWZSquare.shapeZ (outer t)] i).val := by
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
    · simpa only [left, right, Matrix.cons_val_two,
        DWZComponentRestriction.LiftedCoarsePair.leftGrade,
        DWZComponentRestriction.LiftedCoarsePair.rightGrade,
        cwSquarePairGrade] using
        congrArg Fin.val (zWord t).down.2
  have hFineSupport : ∀ t,
      (cwSquareFineSplitGrading K 6).blockTensor
        (fun i ↦ fineSplitGrade (left i t) (right i t)) ≠ 0 := by
    intro t
    have hargs :
        (fun i ↦ fineSplitGrade (left i t) (right i t)) =
          (fun i ↦ ![
            fineSplitGrade
              (addressModeLeftGrade xWord t)
              (addressModeRightGrade xWord t),
            fineSplitGrade
              (addressModeLeftGrade yWord t)
              (addressModeRightGrade yWord t),
            fineSplitGrade (zWord t).leftGrade (zWord t).rightGrade] i) := by
      funext i
      fin_cases i <;> rfl
    exact (blockTensor_ne_zero_congr
      (cwSquareFineSplitGrading K 6) hargs).2 (hSupported t)
  have hZUseful : ∀ (s : Fin 15) (a : Fin 3),
      Fintype.card {t : Fin N // outer t = s ∧ left 2 t = a} =
        DWZTable2Counts.split s a * m := by
    intro s a
    simpa only [left, Matrix.cons_val_two] using hUseful s a
  have h := mme_dwz_table2_useful_z_and_fine_support_implies_step1_xy
    (K := K) 6 m outer left right hCoarse hFineSupport hZUseful
  constructor
  · intro s hs a
    exact h.1 s hs a
  · intro s hs a
    exact h.2 s hs a
