-- Prove2me | Theorems.Thm_mme_released_116_regional_split_mass
-- name    : mme_released_116_regional_split_mass
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:16.220988+00:00
-- url     : https://prove2.me/theorems/a3005939-826d-4a52-ba0c-b607b77df0fa
-- title:
--   Positive regional sizes and exact split masses for (1,1,6)
-- statement:
--   For the six released owner-zero $(1,1,6)$ regions, write $b_r$ for the region weight, $a_{r,c}$ for its split weights and $d=10^{12}$. The integer sizes $n_r=b_rd^3$ and split counts $m_{r,c}=b_ra_{r,c}d^2$ satisfy $$n_r>0,\qquad \sum_c m_{r,c}=n_r.$$ Thus each region has a positive size and a consistent prescribed split histogram.
-- source:
--   Released owner-zero term010 and the integer regional CW extraction interface.

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_regional_split_mass :
    ∀ r : Fin 6, 0 < regionalSize r ∧ ∑ c : Split, splitCount r c = regionalSize r := by sorry
