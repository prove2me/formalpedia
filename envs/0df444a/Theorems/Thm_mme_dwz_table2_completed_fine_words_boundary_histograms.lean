-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_fine_words_boundary_histograms
-- name    : mme_dwz_table2_completed_fine_words_boundary_histograms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:17:40.51298+00:00
-- url     : https://prove2.me/theorems/525bff17-075a-4445-8866-42e31f683f28
-- title:
--   Useful Z words give both Step-1 boundary histograms after X/Y completion
-- statement:
--   Let a literal Table-2 useful block have multiplier $m$, and complete its fine $Z$ word by the canonical fine $X/Y$ selector.  On every component with coarse $Y$ degree zero, the number of positions of shape $s$ satisfying $x_L+a=2$ is exactly $\operatorname{split}(s,a)m$.  Symmetrically, on every component with coarse $X$ degree zero, the number satisfying $y_L+a=2$ is the same prescribed quantity.
--
--   These are exactly the two boundary-survival histograms consumed by DWZ Additional Zeroing-Out Step 1.  The result is an exact finite statement, including $m=0$ and zero Table-2 cells.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 1, conditions (a) and (b), printed pp. 51--52 (PDF pp. 52--53), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_completed_fine_words
import Definitions.Def_mme_dwz_table2_useful_block

open MME
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_completed_fine_words_boundary_histograms
    (m : ℕ) {Position : Type u} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    (∀ (s : Fin 15), MME.DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) ∧
    (∀ (s : Fin 15), MME.DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer t = s ∧
          (completedFineLeft outer small.1 small.2.1 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m) := by
  sorry
