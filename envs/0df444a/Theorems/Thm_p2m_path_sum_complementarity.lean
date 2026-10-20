-- Prove2me | Theorems.Thm_p2m_path_sum_complementarity
-- name    : p2m_path_sum_complementarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:27:10.565901+00:00
-- url     : https://prove2.me/theorems/8cc006a8-22fb-49b6-803f-b817695c8c4e
-- title:
--   p2m_path_sum_complementarity
-- statement:
--   Automatically extracted helper theorem p2m_path_sum_complementarity from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing

section
theorem p2m_path_sum_complementarity {k : ℕ} (x z dx dz : Fin k → ℝ) (μ : ℝ)
    (hcomp : ∀ i, z i * dx i + x i * dz i = μ - x i * z i) :
    (∑ i : Fin k, (z i * dx i + x i * dz i)) =
      (k : ℝ) * μ - z ⬝ᵥ x := by sorry
end
