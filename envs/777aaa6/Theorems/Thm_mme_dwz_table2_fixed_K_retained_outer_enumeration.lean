-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_retained_outer_enumeration
-- name    : mme_dwz_table2_fixed_K_retained_outer_enumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:36:48.177531+00:00
-- url     : https://prove2.me/theorems/eca426cd-67b5-4365-8f3e-650768f4324e
-- title:
--   Exact Fin-indexing of a retained fixed-K Table-2 family
-- statement:
--   Fix a positive Table-2 multiplier and a coarse Z-word K. Every retained subfamily I of the exact fixed-K first-hash target admits an injective enumeration by Fin(|I|) into the literal Outer(K) type. The enumeration has exact two-sided source-word correspondence after undoing the coordinate reindexing: every member of I appears, and every enumerated outer word comes from I. Thus the first-hash Finset can index the Step-2 tensor copies without cardinality loss.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Equation (21), and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_fixed_K_retained_finset_outer_image

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_retained_outer_enumeration
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
      ∃ outer : Fin I.card → Outer,
        Function.Injective outer ∧
        (∀ a ∈ I, ∃ j : Fin I.card,
          (outer j).1 = fun t ↦ a (reindex.symm t)) ∧
        ∀ j : Fin I.card, ∃ a ∈ I,
          (outer j).1 = fun t ↦ a (reindex.symm t) := by
  sorry
