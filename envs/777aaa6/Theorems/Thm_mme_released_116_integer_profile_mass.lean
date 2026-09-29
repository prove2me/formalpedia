-- Prove2me | Theorems.Thm_mme_released_116_integer_profile_mass
-- name    : mme_released_116_integer_profile_mass
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:08:14.308218+00:00
-- url     : https://prove2.me/theorems/8808516c-1419-408b-bc39-55c4a5653252
-- title:
--   Physical child-cell masses for the released (1,1,6) profiles
-- statement:
--   For the integer regional profiles of the released owner-zero $(1,1,6)$ component, every mode $i$ and child cell $(r,c)$ satisfy $$\sum_w\mu_i(r,c,w)=m_{r,c}+m_{r,\bar c}.$$ The right side counts both physical occurrences of the cell, as a left child and as a right child of the complementary split. This is the mass identity required by the integer extraction interface.
-- source:
--   Released owner-zero term010 and the integer regional CW extraction interface.

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by sorry
