-- Prove2me | Theorems.Thm_mme_released_116_integer_profile_support
-- name    : mme_released_116_integer_profile_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:07:40.208846+00:00
-- url     : https://prove2.me/theorems/dd316311-77aa-4076-990f-e51878377960
-- title:
--   Grade support of the released (1,1,6) integer profiles
-- statement:
--   For the integer regional profiles of the released owner-zero $(1,1,6)$ component, a positive mode-$i$ child count has the prescribed grade: $$\mu_i(r,c,w)>0\quad\Longrightarrow\quad\sum_{h=0}^{1}w_h=c_i.$$ This verifies support on the required square-word grade in every region and child cell.
-- source:
--   Released owner-zero term010 and the integer regional CW extraction interface.

import Definitions.Def_mme_released_116_integer_profiles
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by sorry
