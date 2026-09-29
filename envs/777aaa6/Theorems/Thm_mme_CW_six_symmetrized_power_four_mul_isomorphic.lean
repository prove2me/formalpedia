-- Prove2me | Theorems.Thm_mme_CW_six_symmetrized_power_four_mul_isomorphic
-- name    : mme_CW_six_symmetrized_power_four_mul_isomorphic
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:45.085935+00:00
-- url     : https://prove2.me/theorems/34b71878-2387-4225-beb8-37b5d0cb1013
-- title:
--   Six symmetrized CW powers collect into one power
-- statement:
--   The six symmetrization of the four Nth power of CW is isomorphic to its twenty-four Nth power. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_CW_six_fourth_power_isomorphic
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
open MME
universe u

theorem mme_CW_six_symmetrized_power_four_mul_isomorphic
    {K : Type u} [Field K] (q N : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization ((CWObj K q).kronPow (4 * N)))
      ((CWObj K q).kronPow (24 * N)) := by sorry
