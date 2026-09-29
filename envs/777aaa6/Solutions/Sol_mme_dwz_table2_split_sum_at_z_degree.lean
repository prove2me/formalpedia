-- Prove2me | solution 1 for mme_dwz_table2_split_sum_at_z_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:23:07.984079+00:00
-- url     : https://prove2.me/submissions/ed3a33cd-bbbf-4de3-a322-62daecf50426

import Definitions.Def_mme_dwz_table2_step1_z_histogram_fibers

open MME BigOperators
open MME.DWZStep1Histogram

set_option autoImplicit false
set_option warningAsError true

theorem solution (k : Fin 5) (a : Fin 3) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k},
      MME.DWZTable2Counts.split s.1 a) = table2TotalZSplit k a := by
  fin_cases k <;> fin_cases a <;> decide
