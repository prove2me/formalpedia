-- Prove2me | Theorems.Thm_mme_released_116_regional_total
-- name    : mme_released_116_regional_total
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:29.914952+00:00
-- url     : https://prove2.me/theorems/53ada7a3-ac5c-4a8a-8462-66d8d5c685cb
-- title:
--   Total size of the released (1,1,6) regions
-- statement:
--   For $d=10^{12}$ and the six region weights $b_r$ in the released owner-zero $(1,1,6)$ seed, the integer regional sizes $n_r=b_rd^3$ satisfy $$\sum_{r=0}^{5}n_r=d^4.$$ Their total therefore matches the integer scale of the released joint-count row.
-- source:
--   Released owner-zero term010 and the integer regional CW extraction interface.

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_regional_total :
    ∑ r, regionalSize r = denominator ^ 4 := by sorry
