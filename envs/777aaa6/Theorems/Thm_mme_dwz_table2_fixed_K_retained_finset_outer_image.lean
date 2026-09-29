-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_retained_finset_outer_image
-- name    : mme_dwz_table2_fixed_K_retained_finset_outer_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:06:41.182976+00:00
-- url     : https://prove2.me/theorems/3d9ce2bf-9e1c-4326-9614-d51b5aeebcf3
-- title:
--   Coherent Outer image of a fixed-K retained Table-2 family
-- statement:
--   Fix a positive Table-2 multiplier and a coarse Z-word K. For every retained finite subfamily I of the exact fixed-K first-hash target, there is a finite family J of literal Outer(K) words with |J|=|I|. Membership is characterized in both directions by undoing the coordinate reindexing. Thus the whole retained family, not just its individual elements, can index Claim-6.8 broken copies without cardinality loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Equation (21), and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_target_equiv_outer

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_retained_finset_outer_image
    (m : ℕ) (hm : 0 < m)
    (K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5) :
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
    let Outer :=
      {w : Fin L → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Fin L // w t = s} =
          MME.DWZTable2Counts.component s * m}
    ∀ I : Finset (Fin (N + 1) → Fin 15), I ⊆ T →
      ∃ J : Finset Outer,
        J.card = I.card ∧
        (∀ a ∈ I, ∃ w ∈ J,
          w.1 = fun t ↦ a (reindex.symm t)) ∧
        ∀ w ∈ J, ∃ a ∈ I,
          w.1 = fun t ↦ a (reindex.symm t) := by
  sorry
