-- Prove2me | Theorems.Thm_p2m_abs_le_normInf
-- name    : p2m_abs_le_normInf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T15:51:52.105815+00:00
-- url     : https://prove2.me/theorems/7e05747f-d311-45fd-afea-8ac5e32c67a2
-- title:
--   p2m_abs_le_normInf
-- statement:
--   Automatically extracted helper theorem p2m_abs_le_normInf from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_abs_le_normInf {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    |v i| ≤ normInf v := by sorry
