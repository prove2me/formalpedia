-- Prove2me | Theorems.Thm_mme_CW_2376_profile_multiplicity_sum
-- name    : mme_CW_2376_profile_multiplicity_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:56:39.453147+00:00
-- url     : https://prove2.me/theorems/53ab09f3-9a07-4edd-ad2a-1275dcfc4421
-- title:
--   The fifteen CW joint multiplicities sum to the profile length
-- statement:
--   At scale $m$, assign multiplicity $699m$ to each of the three scalar joint types, $37518m$ to each of the six rectangular types, $307638m$ to each of the three central types, $616627m$ to each of the three coupled types, and zero to every unsupported grade triple. Then
--
--   $$
--   \sum_{\sigma}\beta_\sigma=3000000m.
--   $$
--
--   Thus the optimized fifteen-cell joint profile has exactly the prescribed word length used in the outer Coppersmith--Winograd $2.376$ construction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) on pp. 267--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_joint_profile_table
import Theorems.Thm_mme_CW_2376_integer_profile

open MME BigOperators

theorem mme_CW_2376_profile_multiplicity_sum (m : ℕ) :
    (∑ σ : Fin 3 → Fin 5, cw2376ProfileMultiplicity m σ) =
      cw2376ProfileLength m := by
  sorry
