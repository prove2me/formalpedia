-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_target_count_factorization
-- name    : mme_dwz_table2_fixed_K_target_count_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:46:49.236291+00:00
-- url     : https://prove2.me/theorems/d9f248cc-5a86-4770-acb6-2df808825121
-- title:
--   Exact fixed-coarse-Z Table-2 target count
-- statement:
--   Fix any coarse Z-word K with the exact Table-2 coarse histogram. The family O_K of fifteen-valued component words above K with the exact joint histogram has cardinality independent of K, and the exact division-free identity N_alpha = N_BZ |O_K| holds. This is the finite N_alpha/N_BZ target count used in Equation (21), without introducing natural-number division.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and the fixed-Z-block counting in Section 6.2, printed pp. 53-56; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_target_count_factorization
    (m : ℕ)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    (hK : ∀ k,
      Fintype.card {t // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m) :
    let Outer :=
      {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m}
    Nat.multinomial Finset.univ
        (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
      Nat.multinomial Finset.univ
          (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) *
        Nat.card Outer := by
  sorry
