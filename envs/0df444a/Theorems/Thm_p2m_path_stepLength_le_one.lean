-- Prove2me | Theorems.Thm_p2m_path_stepLength_le_one
-- name    : p2m_path_stepLength_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:27:09.389142+00:00
-- url     : https://prove2.me/theorems/4f2b1826-b155-4406-a325-40b88fd96dd8
-- title:
--   p2m_path_stepLength_le_one
-- statement:
--   Automatically extracted helper theorem p2m_path_stepLength_le_one from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

section
theorem p2m_path_stepLength_le_one {m n : ℕ} (r : ℝ) (p d : PDPoint m n) :
    stepLength r p d ≤ 1 := by sorry
end
