-- Prove2me | Theorems.Thm_mme_dwz_table2_outer_card_le_fifteen_pow
-- name    : mme_dwz_table2_outer_card_le_fifteen_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:03:31.109921+00:00
-- url     : https://prove2.me/theorems/ad3b338b-6326-4dcd-aa04-f0ddb3ac8b6d
-- title:
--   Table-2 fixed-coarse-word outer family lies below the ambient word universe
-- statement:
--   For any coarse Z word K of length L, the family of exact Table-2 outer component words above K has at most 15^L elements, since it is a subtype of all length-L words over the fifteen component labels.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, fixed-coarse-Z outer words in Definition 6.6 and Section 6.2, printed pp. 54-57; https://arxiv.org/abs/2210.10173

import Mathlib
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false

theorem mme_dwz_table2_outer_card_le_fifteen_pow
    (L m : ℕ) (K : Fin L → Fin 5) :
    Nat.card
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t : Fin L // w t = s} =
            MME.DWZTable2Counts.component s * m} ≤
      15 ^ L := by
  sorry
