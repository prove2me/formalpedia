-- Prove2me | solution 1 for mme_dwz_table2_completed_useful_family_step1_premises
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:39:15.813341+00:00
-- url     : https://prove2.me/submissions/2ec234b3-9b78-4536-b905-bd019497390e

import Theorems.Thm_mme_dwz_table2_completed_fine_words_equations
import Theorems.Thm_mme_dwz_table2_completed_fine_words_boundary_histograms
import Theorems.Thm_mme_dwz_table2_completed_fine_words_total_z_histogram

open MME
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u v

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  constructor
  · intro j i t
    exact (mme_dwz_table2_completed_fine_words_equations
      (outer j) (small j).1 (small j).2.1).1 i t
  constructor
  · intro j s hs a
    exact (mme_dwz_table2_completed_fine_words_boundary_histograms
      m (outer j) (small j)).1 s hs a
  constructor
  · intro j s hs a
    exact (mme_dwz_table2_completed_fine_words_boundary_histograms
      m (outer j) (small j)).2 s hs a
  · intro j k a
    exact mme_dwz_table2_completed_fine_words_total_z_histogram
      m (outer j) (small j) k a
