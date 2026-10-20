-- Prove2me | Theorems.Thm_p2m_norm1_smul
-- name    : p2m_norm1_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T15:51:47.979979+00:00
-- url     : https://prove2.me/theorems/cba113ed-3650-4b19-83ba-bfd95cd5bc1b
-- title:
--   p2m_norm1_smul
-- statement:
--   Automatically extracted helper theorem p2m_norm1_smul from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_norm1_smul {k : ℕ} (a : ℝ) (ha : 0 ≤ a) (v : Fin k → ℝ) :
    norm1 (a • v) = a * norm1 v := by sorry
