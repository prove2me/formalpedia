-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
-- name    : mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:31:36.522162+00:00
-- url     : https://prove2.me/theorems/7b91580c-e640-4876-88b6-2c7aaf76ef52
-- title:
--   The fixed-K first-hash target is equivalent to the Claim-6.8 outer family
-- statement:
--   Fix a positive Table-2 scale and a coarse Z-word K. The reindexed first-hash target T_K consists of global marginal words with the exact fifteen component multiplicities and pointwise Z-address K. Undoing the affine coordinate reindexing is an explicit equivalence from the subtype of elements of T_K to the literal fixed-K Outer subtype used in Lemma 6.7 and Claim 6.8. In particular |T_K| = |Outer_K| exactly. The reverse map proves, rather than assumes, that exact component counts push forward to all three prescribed marginals.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Equation (21), Lemma 6.7, Equations (22)–(23), and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
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
    ∃ e : {a : Fin (N + 1) → Fin 15 // a ∈ T} ≃ Outer,
      (∀ a, (e a).1 = fun t ↦ a.1 (reindex.symm t)) ∧
      T.card = Nat.card Outer := by
  sorry
