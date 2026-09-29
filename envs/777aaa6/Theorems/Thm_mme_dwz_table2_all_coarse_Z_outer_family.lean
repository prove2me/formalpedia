-- Prove2me | Theorems.Thm_mme_dwz_table2_all_coarse_Z_outer_family
-- name    : mme_dwz_table2_all_coarse_Z_outer_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:07:21.508702+00:00
-- url     : https://prove2.me/theorems/ae6566a2-da88-4cc0-9ec1-adb183ece50c
-- title:
--   Exact NBZ-fold transport of a fixed-coarse-Z retained outer family
-- statement:
--   Fix a prescribed coarse Z word K₀ and any finite retained family I of exact outer component words above it. There are exactly N_BZ prescribed coarse Z words. The product of those words with I is equivalent to Fin(N_BZ·|I|), and every owner in the resulting family lies above its indexed coarse word and is obtained from the corresponding retained K₀-owner by a common fiberwise position permutation preserving all component labels. This is the exact combinatorial restoration of the N_BZ multiplicity in Equation (21); tensor isolation of these owners is a separate step.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21), the fixed-coarse-Z asymmetric hash, and the restoration of all coarse Z words in Section 6.2, printed pp. 53-57; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_all_coarse_Z_words_card
import Theorems.Thm_mme_dwz_table2_outer_equiv_across_coarse_Z_words

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_all_coarse_Z_outer_family
    (m : ℕ)
    (K₀ : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    (hK₀ : ∀ z, Fintype.card {t // K₀ t = z} =
      MME.DWZTable2Counts.alphaZ z * m)
    (I : Type*) [Fintype I]
    (retained : I →
      {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₀ t) ∧
        ∀ s, Fintype.card {t // w t = s} =
          MME.DWZTable2Counts.component s * m}) :
    let CoarseWords :=
      {K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5 //
        ∀ z, Fintype.card {t // K t = z} =
          MME.DWZTable2Counts.alphaZ z * m}
    let NBZ := Nat.multinomial Finset.univ
      (fun z : Fin 5 ↦ MME.DWZTable2Counts.alphaZ z * m)
    ∃ _indexEquiv : Fin (NBZ * Fintype.card I) ≃ (Σ _ : CoarseWords, I),
      ∃ transported : ∀ K : CoarseWords, I →
          {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) = K.1 t) ∧
            ∀ s, Fintype.card {t // w t = s} =
              MME.DWZTable2Counts.component s * m},
        ∀ K, ∃ positionEquiv :
            Fin (MME.DWZTable2Counts.scale * m) ≃
              Fin (MME.DWZTable2Counts.scale * m),
          (∀ t, K.1 (positionEquiv t) = K₀ t) ∧
          ∀ i t, (transported K i).1 (positionEquiv t) =
            (retained i).1 t := by
  sorry
