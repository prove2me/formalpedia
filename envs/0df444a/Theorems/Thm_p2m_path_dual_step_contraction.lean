-- Prove2me | Theorems.Thm_p2m_path_dual_step_contraction
-- name    : p2m_path_dual_step_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:02:28.659571+00:00
-- url     : https://prove2.me/theorems/4d73f59f-084f-46e9-8ba4-a1e06a52563b
-- title:
--   p2m_path_dual_step_contraction
-- statement:
--   Automatically extracted helper theorem p2m_path_dual_step_contraction from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_dual_update
import Theorems.Thm_p2m_path_norm1_smul
import Theorems.Thm_p2m_path_norm1_nonneg
import Theorems.Thm_p2m_path_stepLength_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

section
theorem p2m_path_dual_step_contraction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (ht : t ≤ stepLength r p d) :
    norm1 (dualInfeas A c p') ≤ (1 - t) * norm1 (dualInfeas A c p) := by sorry
end
