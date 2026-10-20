-- Prove2me | Theorems.Thm_p2m_path_normInf_nonneg
-- name    : p2m_path_normInf_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:27:09.868222+00:00
-- url     : https://prove2.me/theorems/bf360083-4e90-4d3f-922c-65c8b95518f8
-- title:
--   p2m_path_normInf_nonneg
-- statement:
--   Automatically extracted helper theorem p2m_path_normInf_nonneg from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
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
theorem p2m_path_normInf_nonneg {k : ℕ} (v : Fin k → ℝ) : 0 ≤ normInf v := by sorry
end
