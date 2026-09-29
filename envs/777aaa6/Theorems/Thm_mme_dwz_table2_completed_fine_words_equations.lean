-- Prove2me | Theorems.Thm_mme_dwz_table2_completed_fine_words_equations
-- name    : mme_dwz_table2_completed_fine_words_equations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:04:49.054826+00:00
-- url     : https://prove2.me/theorems/a060d11d-4c38-4005-9e79-12f33e3d5ffc
-- title:
--   Completed Table-2 fine words satisfy all coarse and half-support equations
-- statement:
--   Let an outer word choose one of the fifteen Table-2 component shapes at every position, and let a fine $Z$ word assign a pair $(z_L,z_R)\in\{0,1,2\}^2$ that coarsens to the selected component's $Z$ degree.  Complete this data by the canonical fine $X/Y$ selector.  Then, for every tensor mode $i\in\{X,Y,Z\}$ and position $t$, the left and right grades add to the corresponding coarse component degree.  Moreover, on both halves of the CW square the three fine grades add to two, and the completed mode-$Z$ coordinates are exactly $z_L$ and $z_R$.
--
--   These identities provide the literal coarse-address and fine-support arithmetic needed by Additional Zeroing-Out Step 1.  They are grade-level facts only: no tensor-nonzero converse and no hole mask is asserted.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1 component decomposition and Section 6.1 Additional Zeroing-Out Step 1, printed pp. 45--52 (PDF pp. 46--53), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_completed_fine_words

open MME
open MME.DWZStep2Source

universe u

set_option autoImplicit false

theorem mme_dwz_table2_completed_fine_words_equations
    {Position : Type u} (outer : Position → Fin 15)
    (z : Position → Fin 3 × Fin 3)
    (hZ : ∀ t, MME.DWZTable2Counts.coarseOf (z t) =
      MME.DWZSquare.shapeZ (outer t)) :
    (∀ i t,
      (completedFineLeft outer z hZ i t).val +
          (completedFineRight outer z hZ i t).val =
        (cwSquareBlockType
          (MME.DWZSquare.shapeX (outer t))
          (MME.DWZSquare.shapeY (outer t))
          (MME.DWZSquare.shapeZ (outer t)) i).val) ∧
    (∀ t,
      (completedFineLeft outer z hZ 0 t).val +
          (completedFineLeft outer z hZ 1 t).val +
          (completedFineLeft outer z hZ 2 t).val = 2) ∧
    (∀ t,
      (completedFineRight outer z hZ 0 t).val +
          (completedFineRight outer z hZ 1 t).val +
          (completedFineRight outer z hZ 2 t).val = 2) ∧
    (∀ t,
      completedFineLeft outer z hZ 2 t = (z t).1 ∧
      completedFineRight outer z hZ 2 t = (z t).2) := by
  sorry
