-- Prove2me | Theorems.Thm_mme_dwz_table2_all_coarse_Z_words_card
-- name    : mme_dwz_table2_all_coarse_Z_words_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:55:03.105418+00:00
-- url     : https://prove2.me/theorems/f85a127e-02a3-48cc-beca-4b909211e4c9
-- title:
--   Exact number of prescribed Table-2 coarse Z words
-- statement:
--   For integral Table-2 scale multiplier m, the family of all length-Mm coarse Z words having exactly m c_z occurrences of each of the five Z labels has cardinality equal to the five-cell multinomial N_BZ=Mult(m c_Z). This identifies the multiplicity which must be restored after performing the asymmetric hash at one fixed coarse word.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and the coarse-Z-word enumeration in Section 6.2, printed pp. 53-56; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_all_coarse_Z_words_card (m : ℕ) :
    Nat.card
        {K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 //
          ∀ z, Fintype.card {t // K t = z} =
            MME.DWZTable2Counts.alphaZ z * m} =
      Nat.multinomial Finset.univ
        (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m) := by
  sorry
