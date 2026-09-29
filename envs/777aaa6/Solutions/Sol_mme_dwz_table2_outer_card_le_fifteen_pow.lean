-- Prove2me | solution 1 for mme_dwz_table2_outer_card_le_fifteen_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:04:21.886837+00:00
-- url     : https://prove2.me/submissions/1d329aee-2512-4f6c-b02c-967a96c8edd6

import Mathlib
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (L m : ℕ) (K : Fin L → Fin 5) :
    Nat.card
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t : Fin L // w t = s} =
            MME.DWZTable2Counts.component s * m} ≤
      15 ^ L := by
  let Outer :=
    {w : Fin L → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m}
  calc
    Nat.card Outer ≤ Nat.card (Fin L → Fin 15) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = 15 ^ L := by simp [Nat.card_eq_fintype_card]
