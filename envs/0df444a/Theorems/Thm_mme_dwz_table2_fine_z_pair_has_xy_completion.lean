-- Prove2me | Theorems.Thm_mme_dwz_table2_fine_z_pair_has_xy_completion
-- name    : mme_dwz_table2_fine_z_pair_has_xy_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T09:44:28.176384+00:00
-- url     : https://prove2.me/theorems/0b957e0b-7445-4f4d-abc4-fa75c984230f
-- title:
--   Every Table-2 fine Z split admits compatible fine X/Y splits
-- statement:
--   Let $(I,J,K)$ be one of the fifteen coarse component shapes in DWZ Table 2, and let $(a,b)\in\{0,1,2\}^2$ be a fine $Z$ split with $a+b=K$. Then there are fine $X$ and $Y$ splits $(x_L,x_R)$ and $(y_L,y_R)$ such that
--
--   $$
--   x_L+x_R=I,\qquad y_L+y_R=J,
--   $$
--
--   while the two Coppersmith--Winograd half-support equations hold:
--
--   $$
--   x_L+y_L+a=2,\qquad x_R+y_R+b=2.
--   $$
--
--   Thus every literal fine $Z$ grade occurring inside a Table-2 component can be completed at grade level to a supported fine triple in the square. This is the local constructor needed to build retained fine X/Y words; it does not assert nonzero tensor coefficients or global histograms.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1 component decomposition and Section 6.1 Additional Zeroing-Out Step 1, printed pp. 45--52 (PDF pp. 46--53), specialized to the fifteen Table-2 level-two shapes; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_pair_coarsening

open MME

set_option autoImplicit false

theorem mme_dwz_table2_fine_z_pair_has_xy_completion
    (s : Fin 15) (zLeft zRight : Fin 3)
    (hZ : MME.DWZTable2Counts.coarseOf (zLeft, zRight) =
      MME.DWZSquare.shapeZ s) :
    ∃ xLeft xRight yLeft yRight : Fin 3,
      xLeft.val + xRight.val = (MME.DWZSquare.shapeX s).val ∧
      yLeft.val + yRight.val = (MME.DWZSquare.shapeY s).val ∧
      xLeft.val + yLeft.val + zLeft.val = 2 ∧
      xRight.val + yRight.val + zRight.val = 2 := by
  sorry
