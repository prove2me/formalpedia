-- Prove2me | Theorems.Thm_p2m_stepLength_le_one
-- name    : p2m_stepLength_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T15:51:50.525985+00:00
-- url     : https://prove2.me/theorems/07a8f011-4aba-4e8a-b9cc-27fc77a17533
-- title:
--   p2m_stepLength_le_one
-- statement:
--   Automatically extracted helper theorem p2m_stepLength_le_one from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_stepLength_le_one {m n : ℕ} (r : ℝ) (p d : PDPoint m n) :
    stepLength r p d ≤ 1 := by sorry
