-- Prove2me | Theorems.Thm_mme_dwz_table2_total_z_split_balance
-- name    : mme_dwz_table2_total_z_split_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:45:42.755247+00:00
-- url     : https://prove2.me/theorems/42a22b47-f77a-4b44-b93a-89eab66ac11f
-- title:
--   Exact Table-2 balance between boundary and interior Z-splits
-- statement:
--   For each coarse $Z$-grade $k$ and left fine grade $a$, the total Table-2 split count is exactly the sum of the contributions from all boundary components of grade $k$ and the contribution from the interior component $(+,+,k)$:
--
--   $$
--   \sum_{s\in\partial_k}\operatorname{split}(s,a)
--   +\operatorname{plusSplit}(k,a)
--   =\sum_{b:\,a+b=k}\gamma_{a,b}.
--   $$
--
--   This finite identity is the arithmetic conservation law used to infer the interior Step-1 histogram after the boundary histograms have been forced by fine CW support.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Table 2 and Additional Zeroing-Out Step 1 in Section 6.1. https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open BigOperators
open MME MME.DWZStep1Histogram

set_option autoImplicit false

theorem mme_dwz_table2_total_z_split_balance (k : Fin 5) (a : Fin 3) :
    (∑ s : BoundaryComponentAt k, MME.DWZTable2Counts.split s.1 a) +
      MME.DWZTable2Counts.plusSplit k a = table2TotalZSplit k a := by
  sorry
