-- Prove2me | Theorems.Thm_mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero
-- name    : mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T11:08:16.635531+00:00
-- url     : https://prove2.me/theorems/1efd536c-5399-4182-8b6d-97fce46fcfb7
-- title:
--   Coordinate support kills every Y word rejected after Step-1 X filtering
-- statement:
--   For one broken owner, assume every selected X/Y/Z word triple containing a zero fine coordinate is annihilated. After inserting the Step-1 X boundary-histogram filter, every canonical Y address word rejected by the Y histogram filter is annihilated.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_rejected_singleton_properties

open MME Module PiTensorProduct
open MME.DWZStep1Support
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_y_rejected_singletons_zero_of_coordinate_word_zero
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (hCoordinateZero : BrokenOwnerCoordinateZeroProperty
      K m outer copy) :
    Step1YRejectedSingletonZeroProperty K m outer copy := by
  sorry
