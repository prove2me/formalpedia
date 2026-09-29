-- Prove2me | Theorems.Thm_mme_CW_six_fourth_power_isomorphic
-- name    : mme_CW_six_fourth_power_isomorphic
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:36:41.213712+00:00
-- url     : https://prove2.me/theorems/37f3cee6-178b-45f8-9ce8-6e791597068c
-- title:
--   Six-symmetrized CW fourth powers have 24 elementary factors
-- statement:
--   For every field $K$ and natural numbers $q,n$, the $n$th tensor power of the six-symmetrization of the fourth Coppersmith–Winograd power is isomorphic to $\mathrm{CW}_q^{\otimes 24n}$. The isomorphism uses the cyclic and transposition symmetries of the CW tensor and the associativity and commutativity of tensor products up to isomorphism. This identifies the elementary CW exponent of the ambient source; it does not supply the stage extraction or repair-budget witnesses.
-- source:
--   Direct tensor symmetry and quotient-semiring calculation.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open MME PiTensorProduct BigOperators
universe u
set_option autoImplicit false

theorem mme_CW_six_fourth_power_isomorphic
    {K : Type u} [Field K] (q n : ℕ) :
    TensorObj.Isomorphic
      ((sixSymmetrization (StothersFourth.cwFourthObj K q)).kronPow n)
      ((CWObj K q).kronPow (24 * n)) := by sorry
