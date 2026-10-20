-- Prove2me | Theorems.Thm_p2m_path_norm1_smul
-- name    : p2m_path_norm1_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:27:12.024183+00:00
-- url     : https://prove2.me/theorems/3ea575c1-0445-4852-8095-8d403dcd7017
-- title:
--   p2m_path_norm1_smul
-- statement:
--   Automatically extracted helper theorem p2m_path_norm1_smul from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
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
theorem p2m_path_norm1_smul {k : ℕ} (a : ℝ) (ha : 0 ≤ a) (v : Fin k → ℝ) :
    norm1 (a • v) = a * norm1 v := by sorry
end
