-- Prove2me | Theorems.Thm_mme_dwz_table2_split_sum_at_z_degree
-- name    : mme_dwz_table2_split_sum_at_z_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T10:21:59.801774+00:00
-- url     : https://prove2.me/theorems/af1e300c-bfbe-420f-9ed2-bc962f61b469
-- title:
--   Table-2 component splits sum to the total-Z split histogram
-- statement:
--   For every coarse $Z$ degree $k\in\{0,1,2,3,4\}$ and left fine grade $a\in\{0,1,2\}$, sum the literal Table-2 split count $\operatorname{split}(s,a)$ over all fifteen component rows $s$ whose coarse $Z$ degree is $k$.  The result is exactly
--
--   $$
--   \operatorname{TotalZSplit}(k,a)=\sum_{b=0}^2 [a+b=k]\,\gamma(a,b).
--   $$
--
--   This finite identity is the arithmetic bridge from per-component useful-block fibers to the total-$Z$ histogram used in Additional Zeroing-Out Step 1.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and Additional Zeroing-Out Step 1 condition (c), printed pp. 51--52 (PDF pp. 52--53); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open MME BigOperators
open MME.DWZStep1Histogram

set_option autoImplicit false

theorem mme_dwz_table2_split_sum_at_z_degree
    (k : Fin 5) (a : Fin 3) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
      MME.DWZTable2Counts.split s.1 a) = table2TotalZSplit k a := by
  sorry
