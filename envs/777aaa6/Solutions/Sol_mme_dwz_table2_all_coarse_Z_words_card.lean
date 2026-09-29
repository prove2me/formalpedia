-- Prove2me | solution 1 for mme_dwz_table2_all_coarse_Z_words_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T18:03:33.695505+00:00
-- url     : https://prove2.me/submissions/5e2f735c-1b76-4035-a7e0-fbf5e31be740

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem prescribed_fiber_nat_card
    {Position Label : Type*}
    [Fintype Position] [DecidableEq Position]
    [Fintype Label] [DecidableEq Label]
    (counts : Label → ℕ)
    (hsum : ∑ i, counts i = Fintype.card Position) :
    Nat.card
        {f : Position → Label //
          ∀ i, Fintype.card {t : Position // f t = i} = counts i} =
      Nat.multinomial Finset.univ counts := by
  have h := mme_fintype_prescribed_fiber_function_card counts hsum
  rw [← Nat.card_eq_fintype_card] at h
  simpa only [Nat.multinomial, hsum] using h

theorem solution (m : ℕ) :
    Nat.card
        {K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 //
          ∀ z, Fintype.card {t // K t = z} =
            MME.DWZTable2Counts.alphaZ z * m} =
      Nat.multinomial Finset.univ
        (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) := by
  classical
  have hzsum :
      (∑ z : Fin 5, MME.DWZTable2Counts.alphaZ z * m) =
        Fintype.card (Fin (MME.DWZTable2Counts.scale * m)) := by
    rw [← Finset.sum_mul]
    rw [mme_dwz_table2_integer_counts_exact.2.2.2.2.2.1]
    simp
  exact prescribed_fiber_nat_card
    (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) hzsum
