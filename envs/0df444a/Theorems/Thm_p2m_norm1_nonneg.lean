-- Prove2me | Theorems.Thm_p2m_norm1_nonneg
-- name    : p2m_norm1_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T15:51:59.322099+00:00
-- url     : https://prove2.me/theorems/257f57be-3566-4086-a249-022748ca0204
-- title:
--   p2m_norm1_nonneg
-- statement:
--   Automatically extracted helper theorem p2m_norm1_nonneg from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_norm1_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ norm1 v := by sorry
