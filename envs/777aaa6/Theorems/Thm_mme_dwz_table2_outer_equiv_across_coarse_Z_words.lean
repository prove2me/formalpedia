-- Prove2me | Theorems.Thm_mme_dwz_table2_outer_equiv_across_coarse_Z_words
-- name    : mme_dwz_table2_outer_equiv_across_coarse_Z_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:54:41.860991+00:00
-- url     : https://prove2.me/theorems/4381eab7-7ed8-4e83-8538-079a05c3fdb6
-- title:
--   Fiberwise transport of Table-2 outer families across coarse Z words
-- statement:
--   Any two length-L coarse Z words with the same exact Table-2 histogram are related by a position permutation matching each Z fiber. This permutation induces an equivalence between their exact outer component-word families, and transported outer words preserve every component label pointwise under the same permutation. Thus a retained fixed-coarse-Z owner can be transported source-faithfully to every other prescribed coarse word.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, the fixed-coarse-Z decomposition surrounding Equation (21), Definition 6.6, and Claim 6.8 in Section 6.2, printed pp. 53-57; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_square_data

set_option autoImplicit false

theorem mme_dwz_table2_outer_equiv_across_coarse_Z_words
    (m : ℕ) {L : ℕ} (K₁ K₂ : Fin L → Fin 5)
    (hK₁ : ∀ z, Fintype.card {t : Fin L // K₁ t = z} =
      MME.DWZTable2Counts.alphaZ z * m)
    (hK₂ : ∀ z, Fintype.card {t : Fin L // K₂ t = z} =
      MME.DWZTable2Counts.alphaZ z * m) :
    let Outer₁ :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₁ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Outer₂ :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K₂ t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    ∃ e : Fin L ≃ Fin L, (∀ t, K₂ (e t) = K₁ t) ∧
      ∃ E : Outer₁ ≃ Outer₂,
        ∀ w t, (E w).1 (e t) = w.1 t := by
  sorry
