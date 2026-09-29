-- Prove2me | solution 1 for mme_dwz_table2_standard_block_card_le_two_pow_four_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:26:14.088437+00:00
-- url     : https://prove2.me/submissions/ac2b0ae9-1776-4c0e-be23-b8e603317210

import Definitions.Def_mme_dwz_standard_labelled_z_blocks
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution (m : ℕ) :
    Fintype.card (MME.DWZComponentRestriction.DWZStandardBlock m) ≤
      2 ^ (4 * (MME.DWZTable2Counts.scale * m)) := by
  classical
  let Position := MME.DWZComponentRestriction.GroupedPosition m
  calc
    Fintype.card (MME.DWZComponentRestriction.DWZStandardBlock m) ≤
        Fintype.card (Position → Fin 3 × Fin 3) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 9 ^ Fintype.card Position := by
      simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
    _ = 9 ^ (MME.DWZTable2Counts.scale * m) := by
      congr 1
      dsimp only [Position, MME.DWZComponentRestriction.GroupedPosition]
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin, ← Finset.sum_mul]
      exact congrArg (· * m) mme_dwz_table2_integer_counts_exact.2.2.2.1
    _ ≤ 16 ^ (MME.DWZTable2Counts.scale * m) := by
      exact Nat.pow_le_pow_left (by norm_num : 9 ≤ 16)
        (MME.DWZTable2Counts.scale * m)
    _ = 2 ^ (4 * (MME.DWZTable2Counts.scale * m)) := by
      calc
        16 ^ (MME.DWZTable2Counts.scale * m) =
            (2 ^ 4) ^ (MME.DWZTable2Counts.scale * m) := by norm_num
        _ = 2 ^ (4 * (MME.DWZTable2Counts.scale * m)) := by
          rw [← pow_mul]
