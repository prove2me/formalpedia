-- Prove2me | Theorems.Thm_p2m_path_complementarity_step
-- name    : p2m_path_complementarity_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:02:37.845861+00:00
-- url     : https://prove2.me/theorems/3df23fd2-b54a-40f5-b23f-47ff69b90fc7
-- title:
--   p2m_path_complementarity_step
-- statement:
--   Automatically extracted helper theorem p2m_path_complementarity_step from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_sum_complementarity
import Theorems.Thm_p2m_path_barrierParam_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

section
theorem p2m_path_complementarity_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (M : ℝ) (hx : normInf p.x ≤ M) (hy : normInf p.y ≤ M) :
    complementarity p' ≤
      (1 - (1 - δ) * stepLength r p d) * complementarity p
        + M * norm1 (primalInfeas A b p) + M * norm1 (dualInfeas A c p) := by sorry
end
