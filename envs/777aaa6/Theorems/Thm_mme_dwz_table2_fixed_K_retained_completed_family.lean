-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_retained_completed_family
-- name    : mme_dwz_table2_fixed_K_retained_completed_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:26:08.638617+00:00
-- url     : https://prove2.me/theorems/86edb615-1c43-4551-9de5-163595503bde
-- title:
--   The fixed-K first-hash family has an exact Fin enumeration with completed fine words
-- statement:
--   Fix a positive Table-2 multiplier $m$, a common coarse $Z$ word $K$, and a retained first-hash subfamily $I$ whose coarse $Y$ words are isolated. Then the accepted lossless enumeration produces exactly $|I|$ outer words indexed by $\operatorname{Fin}(|I|)$, with an injective index map and exact correspondence in both directions with $I$. All enumerated copies share $K$, and equality of their coarse $Y$ words forces equality of their indices. Moreover, after choosing any literal useful fine-$Z$ block over every enumerated outer word, the canonical completed fine words satisfy the pointwise CW-square grade equation together with the exact two boundary histograms and total-$Z$ histogram required by DWZ Step 1.
--
--   This capstone preserves the retained family word-for-word and supplies the concrete source data for the Step-2 direct-sum restriction; it introduces neither a cardinality proxy nor a hole-mask assumption.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Additional Zeroing-Out Steps 1 and 2, printed pp. 46--54 (PDF pp. 47--55); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_fixed_K_retained_outer_enumeration
import Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
import Theorems.Thm_mme_dwz_retained_enumeration_common_z_y_isolated

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_retained_completed_family
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
      (∀ a ∈ I, ∀ b ∈ I,
        (fun t ↦ MME.DWZSquare.shapeY (a t)) =
            (fun t ↦ MME.DWZSquare.shapeY (b t)) → a = b) →
      ∃ outer : Fin I.card → Outer,
        Function.Injective outer ∧
        (∀ a ∈ I, ∃ j : Fin I.card,
          (outer j).1 = fun t ↦ a (reindex.symm t)) ∧
        (∀ j : Fin I.card, ∃ a ∈ I,
          (outer j).1 = fun t ↦ a (reindex.symm t)) ∧
        (∀ j j' t,
          MME.DWZSquare.shapeZ ((outer j).1 t) =
            MME.DWZSquare.shapeZ ((outer j').1 t)) ∧
        (∀ j j',
          (fun t ↦ MME.DWZSquare.shapeY ((outer j).1 t)) =
              (fun t ↦ MME.DWZSquare.shapeY ((outer j').1 t)) →
            j = j') ∧
        ∀ small : ∀ j : Fin I.card,
            MME.DWZTable2StandardForm.UsefulBlock m (outer j).1,
          (∀ j i t,
            (MME.DWZStep2Source.completedFineLeft
                (outer j).1 (small j).1 (small j).2.1 i t).val +
                (MME.DWZStep2Source.completedFineRight
                  (outer j).1 (small j).1 (small j).2.1 i t).val =
              (MME.cwSquareBlockType
                (MME.DWZSquare.shapeX ((outer j).1 t))
                (MME.DWZSquare.shapeY ((outer j).1 t))
                (MME.DWZSquare.shapeZ ((outer j).1 t)) i).val) ∧
          (∀ j (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
            ∀ a : Fin 3,
              Fintype.card {t : Fin L //
                (outer j).1 t = s ∧
                (MME.DWZStep2Source.completedFineLeft
                    (outer j).1 (small j).1 (small j).2.1 0 t).val +
                  a.val = 2} =
                MME.DWZTable2Counts.split s a * m) ∧
          (∀ j (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
            ∀ a : Fin 3,
              Fintype.card {t : Fin L //
                (outer j).1 t = s ∧
                (MME.DWZStep2Source.completedFineLeft
                    (outer j).1 (small j).1 (small j).2.1 1 t).val +
                  a.val = 2} =
                MME.DWZTable2Counts.split s a * m) ∧
          ∀ j (z : Fin 5) (a : Fin 3),
            Fintype.card
                (MME.DWZStep1Histogram.TotalZFiber (outer j).1
                  (MME.DWZStep2Source.completedFineLeft
                    (outer j).1 (small j).1 (small j).2.1 2) z a) =
              MME.DWZStep1Histogram.table2TotalZSplit z a * m := by
  sorry
