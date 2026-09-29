-- Prove2me | Theorems.Thm_mme_dwz_completed_fine_z_address_eq_useful_block_encode
-- name    : mme_dwz_completed_fine_z_address_eq_useful_block_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:11:00.480715+00:00
-- url     : https://prove2.me/theorems/3c752b36-0311-4595-aa9e-4c1c700f76be
-- title:
--   A completed Table-2 useful block has its literal encoded fine-Z address
-- statement:
--   Fix a family of retained Table-2 outer component words and one literal useful fine-$Z$ block in each copy. Complete every useful block with the canonical fine $X/Y$ grades. Then the completed grading address in tensor mode $2$ is exactly the pointwise fine-nine encoding of the two grades in the original useful $Z$-pair word:
--
--   $$
--   A_j^{(2)}(t)=\operatorname{encode}(z_j^{\mathrm L}(t),z_j^{\mathrm R}(t)).
--   $$
--
--   This equality is the type bridge from the `UsefulBlock` representation produced by Claim 6.8 to the address-function representation consumed by the Step-2 tensor restriction. It is valid for arbitrary finite position types and includes empty position types.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3 and Additional Zeroing-Out Step 2, printed pp. 51-54 (PDF pp. 52-55); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_retained_fine_address

open MME
open MME.DWZStep1Support
open MME.DWZStep2Source

universe u v

set_option autoImplicit false

theorem mme_dwz_completed_fine_z_address_eq_useful_block_encode
    (m : ℕ) {Copy : Type v} {Position : Type u} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j))
    (j : Copy) :
    let left : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineLeft (outer j') (small j').1 (small j').2.1
    let right : Copy → Fin 3 → Position → Fin 3 := fun j' ↦
      completedFineRight (outer j') (small j').1 (small j').2.1
    retainedFineAddress left right j 2 =
      fun t ↦ fineSplitGrade ((small j).1 t).1 ((small j).1 t).2 := by
  sorry
