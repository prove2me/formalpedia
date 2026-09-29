-- Prove2me | solution 1 for mme_dwz_table2_regional_splits_aggregate_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T13:28:37.247119+00:00
-- url     : https://prove2.me/submissions/1ea98bee-8c22-4b42-9dff-5852f38457f3

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_pair_coarsening

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution (p : Fin 3 × Fin 3) :
    (∑ s : Fin 15,
      if (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
          MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s p.1
      else 0) +
      MME.DWZTable2Counts.plusSplit
        (MME.DWZTable2Counts.coarseOf p) p.1 =
      MME.DWZTable2Counts.gamma p := by
  rcases p with ⟨l, r⟩
  fin_cases l <;> fin_cases r <;>
    norm_num [MME.DWZSquare.shapeX, MME.DWZSquare.shapeY,
      MME.DWZSquare.shapeZ, MME.DWZTable2Counts.coarseOf,
      MME.DWZTable2Counts.split, MME.DWZTable2Counts.plusSplit,
      MME.DWZTable2Counts.gamma, Fin.sum_univ_succ] <;>
    split_ifs <;> norm_num at * <;>
    simp only [Fin.ext_iff] at * <;> omega
