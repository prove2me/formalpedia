-- Prove2me | Theorems.Thm_mme_schonhage_direct_sum
-- name    : mme_schonhage_direct_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-28T14:38:59.038313+00:00
-- url     : https://prove2.me/theorems/43cc09aa-abd6-4d49-ac1b-61739ebe8d8b
-- statement:
--   **Schönhage's direct-sum construction.** The direct sum $\langle 4,1,4\rangle \oplus \langle 1,9,1\rangle$ has asymptotic rank at most $4\cdot 4+1 = 17$, via an explicit degeneration into the unit tensor of border rank $17$. Fed into the sum inequality this yields $16^{\omega/3}+9^{\omega/3}\le 17$.
-- source:
--   https://www.math.ias.edu/~avi/PUBLICATIONS/WigdersonZu_Final_Draft_Oct2023.pdf

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_tensor_rank
universe u
open MME

theorem mme_schonhage_direct_sum {K : Type u} [Field K] :
    tensorAsymptoticRank (TensorObj.bigAdd ![MMObj K 4 1 4, MMObj K 1 9 1]) ≤ 17 := by sorry
