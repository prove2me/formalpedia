-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_fixed_K_target_count_factorization
-- name    : mme_dwz_table2_reindexed_fixed_K_target_count_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:12:31.06919+00:00
-- url     : https://prove2.me/theorems/9644de8f-d414-4bc2-a1db-544a91f5cf3a
-- title:
--   Exact cardinal of the reindexed fixed-coarse-Z Table-2 hash target
-- statement:
--   For every positive integral Table-2 scale multiplier and every coarse Z-word K with the exact prescribed histogram, the literal reindexed target finset T used by the common-prime asymmetric-hashing theorem has the exact division-free cardinal identity N_alpha = N_BZ |T|. This connects the source multinomial quotient directly to the finite target object consumed by the hashing formalization.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21) and the fixed-Z-block counting in Section 6.2, printed pp. 53-56; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
import Theorems.Thm_mme_dwz_table2_fixed_K_target_count_factorization

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_reindexed_fixed_K_target_count_factorization
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5)
    (hK : ∀ k,
      Fintype.card {t // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
      { toFun := fun w t ↦ w (reindex t)
        invFun := fun w t ↦ w (reindex.symm t)
        left_inv := fun w ↦ by funext t; simp
        right_inv := fun w ↦ by funext t; simp }
    let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
    let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let T := A.filter FixedK
    Nat.multinomial Finset.univ
        (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
      Nat.multinomial Finset.univ
          (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) * T.card := by
  sorry
