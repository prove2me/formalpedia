-- Prove2me | Theorems.Thm_p2m_normInf_nonneg
-- name    : p2m_normInf_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:25:27.54061+00:00
-- url     : https://prove2.me/theorems/71e17d3e-e65d-4cee-a20c-64a31dda8f31
-- title:
--   p2m_normInf_nonneg
-- statement:
--   Automatically extracted helper theorem p2m_normInf_nonneg from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_abs_le_normInf
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_normInf_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ normInf v := by sorry
