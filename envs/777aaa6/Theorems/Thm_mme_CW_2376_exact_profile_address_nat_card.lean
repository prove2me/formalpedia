-- Prove2me | Theorems.Thm_mme_CW_2376_exact_profile_address_nat_card
-- name    : mme_CW_2376_exact_profile_address_nat_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:51:36.663604+00:00
-- url     : https://prove2.me/theorems/133ce024-1243-4394-8e70-016c43d7287b
-- title:
--   Exact cardinality of the optimized fifteen-cell CW profile
-- statement:
--   At scale $m$, let $N=3{,}000{,}000m$ and prescribe the fifteen joint-type multiplicities $β_σ$ of equation (13). The number of exact-profile addresses is
--
--   $$
--   rac{N!}{∏_{σ∈Σ}β_σ!}.
--   $$
--
--   Unsupported joint types have multiplicity zero, so their factorials contribute one. This is the exact multinomial target-edge count used in the outer Coppersmith--Winograd hashing argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) and multinomial counts on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_joint_profile_table
import Theorems.Thm_mme_CW_2376_profile_multiplicity_sum
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_2376_exact_profile_address_nat_card (m : ℕ) :
    Nat.card (CW2376ExactProfileAddress m) =
      (cw2376ProfileLength m).factorial /
        ∏ sigma : CW2376SupportedJointType,
          (cw2376TargetJointTable m sigma).factorial := by
  sorry
