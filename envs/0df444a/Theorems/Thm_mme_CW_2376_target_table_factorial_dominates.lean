-- Prove2me | Theorems.Thm_mme_CW_2376_target_table_factorial_dominates
-- name    : mme_CW_2376_target_table_factorial_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:27:41.63736+00:00
-- url     : https://prove2.me/theorems/1f6f7f5f-fb26-4d91-b8c7-ecdfd2cc0f97
-- title:
--   The optimized CW joint table minimizes the factorial denominator at fixed marginals
-- statement:
--   Among all multiplicity tables on the fifteen supported squared Coppersmith--Winograd joint types having the prescribed equation-(13) marginal in every tensor mode and grade, the optimized target table minimizes the product of cell factorials. Equivalently, its associated multinomial completion term is maximal.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates
import Theorems.Thm_mme_CW_2376_target_joint_table_marginal

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mme_CW_2376_target_table_factorial_dominates
    (m : ℕ) (hm : 0 < m) (k : CW2376JointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ r : Fin 5,
      (∑ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 l = r}, k sigma.1) =
        cw2376MarginalMultiplicity m r) :
    (∏ sigma : CW2376SupportedJointType,
        (cw2376TargetJointTable m sigma).factorial) ≤
      ∏ sigma : CW2376SupportedJointType, (k sigma).factorial := by
  sorry
