-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_useful_family_step1_premises
-- name    : mme_dwz_table2_completed_useful_family_step1_premises
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:37:05.668866+00:00
-- url     : https://prove2.me/theorems/66bd3add-8abe-4af0-af99-cbe1ba5e869e
-- title:
--   A family of Table-2 useful blocks supplies every concrete Step-1 premise
-- statement:
--   Let a finite position set carry a family of retained Table-2 outer words, one for each copy $j$.  Suppose each copy is equipped with a literal useful fine-$Z$ block of multiplier $m$.  Complete every fine-$Z$ pair by the canonical fine $X/Y$ selector.  Then the resulting left/right grade words satisfy simultaneously: (i) all three pointwise coarse-address equations; (ii) the exact X-boundary survival histogram; (iii) the exact Y-boundary survival histogram; and (iv) the exact total-$Z$ histogram.
--
--   These are precisely the four concrete premises used by DWZ Additional Zeroing-Out Step 1 for each retained copy.  The statement is exact and finite, including $m=0$ and zero cells; it makes no hole-mask or tensor-nonzero claim.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1 and Additional Zeroing-Out Step 1, printed pp. 45--52 (PDF pp. 46--53), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_completed_fine_words_equations
import Theorems.Thm_mme_dwz_table2_completed_fine_words_boundary_histograms
import Theorems.Thm_mme_dwz_table2_completed_fine_words_total_z_histogram

open MME
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u v

set_option autoImplicit false

theorem mme_dwz_table2_completed_useful_family_step1_premises
    (m : ℕ) {Copy : Type v} {Position : Type u} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (small : ∀ j : Copy,
      MME.DWZTable2StandardForm.UsefulBlock m (outer j)) :
    (∀ j i t,
      (completedFineLeft (outer j) (small j).1 (small j).2.1 i t).val +
          (completedFineRight (outer j) (small j).1 (small j).2.1 i t).val =
        (cwSquareBlockType
          (MME.DWZSquare.shapeX (outer j t))
          (MME.DWZSquare.shapeY (outer j t))
          (MME.DWZSquare.shapeZ (outer j t)) i).val) ∧
    (∀ j (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧
          (completedFineLeft (outer j) (small j).1 (small j).2.1 0 t).val +
            a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ j (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧
          (completedFineLeft (outer j) (small j).1 (small j).2.1 1 t).val +
            a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ j (k : Fin 5) (a : Fin 3),
      Fintype.card
          (TotalZFiber (outer j)
            (completedFineLeft (outer j) (small j).1 (small j).2.1 2) k a) =
        table2TotalZSplit k a * m) := by
  sorry
