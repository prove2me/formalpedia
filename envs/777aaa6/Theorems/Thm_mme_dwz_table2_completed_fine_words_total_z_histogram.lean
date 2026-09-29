-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_fine_words_total_z_histogram
-- name    : mme_dwz_table2_completed_fine_words_total_z_histogram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:28:57.34841+00:00
-- url     : https://prove2.me/theorems/5e8f6ad6-fada-4cfc-9e0e-c427df00ebae
-- title:
--   Completed useful words have the exact Step-1 total-Z histogram
-- statement:
--   Let a literal Table-2 useful block have multiplier $m$, and complete its fine $Z$ word by the canonical fine $X/Y$ selector.  For every coarse $Z$ degree $k$ and left fine grade $a$, the number of positions whose outer row has $Z$ degree $k$ and whose completed left $Z$ grade is $a$ equals
--
--   $$
--   \operatorname{TotalZSplit}(k,a)m.
--   $$
--
--   This is exactly the total-$Z$ histogram premise consumed by DWZ Additional Zeroing-Out Step 1.  It follows by a disjoint decomposition over the fifteen literal component rows and remains exact for $m=0$ and zero cells.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1 condition (c), printed pp. 51--52 (PDF pp. 52--53), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block
import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers
import Theorems.Thm_mme_dwz_table2_split_sum_at_z_degree

open MME BigOperators
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_completed_fine_words_total_z_histogram
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card
          (TotalZFiber outer
            (completedFineLeft outer small.1 small.2.1 2) k a) =
        table2TotalZSplit k a * m := by
  sorry
