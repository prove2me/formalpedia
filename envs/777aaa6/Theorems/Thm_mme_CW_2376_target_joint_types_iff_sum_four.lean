-- Prove2me | Theorems.Thm_mme_CW_2376_target_joint_types_iff_sum_four
-- name    : mme_CW_2376_target_joint_types_iff_sum_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:37:20.068289+00:00
-- url     : https://prove2.me/theorems/42ff05f5-ea79-4bb6-a7f5-9d3633bc7319
-- title:
--   The fifteen CW joint types are exactly the five-grade triples summing to four
-- statement:
--   A triple of grades $σ=(σ_0,σ_1,σ_2)∈{0,1,2,3,4}^3$ belongs to the explicitly enumerated fifteen-type support used by the Coppersmith--Winograd profile if and only if
--
--   $$
--   σ_0+σ_1+σ_2=4.
--   $$
--
--   This equivalence connects the finite equation-(13) type list to the coordinatewise grade-sum-four support condition used by the ambient hypergraph.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the fifteen constituents in equations (12)--(13), journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_joint_profile_table

open MME

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_CW_2376_target_joint_types_iff_sum_four
    (sigma : Fin 3 → Fin 5) :
    sigma ∈ cw2376TargetJointTypes ↔
      (sigma 0).val + (sigma 1).val + (sigma 2).val = 4 := by
  sorry
