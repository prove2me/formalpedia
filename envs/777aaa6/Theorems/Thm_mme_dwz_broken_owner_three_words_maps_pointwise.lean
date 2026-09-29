-- Prove2me | Theorems.Thm_mme_dwz_broken_owner_three_words_maps_pointwise
-- name    : mme_dwz_broken_owner_three_words_maps_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:50:37.366916+00:00
-- url     : https://prove2.me/theorems/4dd55aff-feee-40c8-9e36-ff96e83cb43a
-- title:
--   Dependent and update presentations of three selected owner maps agree
-- statement:
--   For each of the three tensor modes, selecting the packaged X, Y, or Z address word and then applying the broken-owner block projection is identical to the literal nested-update presentation of the three singleton projectors.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_broken_owner_three_words_data

open MME Module
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_broken_owner_three_words_maps_pointwise
    {K : Type u} [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (x : AddressModeWord outer 0)
    (y : AddressModeWord outer 1)
    (z : AddressZWord outer) (i : Fin 3) :
    brokenOwnerThreeWordsWordMap K m outer copy x y z i =
      brokenOwnerThreeWordsSelectedMap K m outer copy x y z i := by
  sorry
