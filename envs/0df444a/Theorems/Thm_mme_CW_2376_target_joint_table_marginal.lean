-- Prove2me | Theorems.Thm_mme_CW_2376_target_joint_table_marginal
-- name    : mme_CW_2376_target_joint_table_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:24:08.028931+00:00
-- url     : https://prove2.me/theorems/4ab9d2ee-b338-4d1b-b374-29b70ef02deb
-- title:
--   The optimized fifteen-cell CW table has the prescribed five-grade marginals
-- statement:
--   For the optimized squared Coppersmith--Winograd joint table at scale $m$, fix any tensor mode and any one of its five grades. The sum of the multiplicities of all supported joint types having that grade in the fixed mode is exactly the prescribed marginal multiplicity for that grade. Thus the explicit fifteen-cell equation-(13) table has the same five-grade marginal in all three modes.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), optimized profile equation (13) on journal p. 268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_joint_tables

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mme_CW_2376_target_joint_table_marginal
    (m : ℕ) (i : Fin 3) (r : Fin 5) :
    (∑ sigma : {sigma : CW2376SupportedJointType // sigma.1 i = r},
      cw2376TargetJointTable m sigma.1) =
        cw2376MarginalMultiplicity m r := by
  sorry
