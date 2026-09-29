-- Prove2me | Theorems.Thm_mme_dwz_table2_retained_fine_address_xy_owner
-- name    : mme_dwz_table2_retained_fine_address_xy_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:18:34.52325+00:00
-- url     : https://prove2.me/theorems/ea0e9e8c-8b2f-47be-9292-a554809b3001
-- title:
--   Fine support and first-hash isolation identify the retained X/Y owner
-- statement:
--   Let a retained family of Table-2 component words be refined at every tensor-power position by the canonical nine-grading of $CW_q\otimes CW_q$. Assume: (1) every fine pair coarsens to the corresponding Table-2 mode degree; (2) all retained words share the same coarse $Z$ word; and (3) distinct retained words have distinct $Y$ words, as guaranteed by the first asymmetric hash.
--
--   For any mixed choice $(j_0,j_1,j_2)$ of retained copies, coordinatewise nonzero fine support implies
--
--   $$
--   j_0=j_1.
--   $$
--
--   Thus canonical fine support and the fixed-$Z$ first-hash family supply exactly the X/Y-owner hypothesis needed by the Step-2 nonhole direct-sum restriction. No block count, dimension comparison, or hole-mask conclusion is asserted.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1 Step 3 and Additional Zeroing-Out Step 1, printed pp. 51--52 (PDF pp. 52--53), together with the canonical fine support equation for the squared CW tensor; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_address
import Theorems.Thm_mme_CW_square_fine_split_support
import Definitions.Def_mme_dwz_square_data

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_retained_fine_address_xy_owner
    (K : Type u) [Field K] (q : ℕ)
    {Copy Position : Type*}
    (outer : Copy → Position → Fin 15)
    (left right : Copy → Fin 3 → Position → Fin 3)
    (hCoarse : ∀ j i r,
      (left j i r).val + (right j i r).val =
        (cwSquareBlockType
          (DWZSquare.shapeX (outer j r))
          (DWZSquare.shapeY (outer j r))
          (DWZSquare.shapeZ (outer j r)) i).val)
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
        (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j') :
    ∀ js : Fin 3 → Copy,
      (∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      js 0 = js 1 := by
  sorry
