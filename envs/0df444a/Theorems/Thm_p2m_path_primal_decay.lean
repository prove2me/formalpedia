-- Prove2me | Theorems.Thm_p2m_path_primal_decay
-- name    : p2m_path_primal_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:09:37.626776+00:00
-- url     : https://prove2.me/theorems/5733fe98-bf53-4b71-a5ad-4f64af12758c
-- title:
--   p2m_path_primal_decay
-- statement:
--   Automatically extracted helper theorem p2m_path_primal_decay from oversized parent candidate deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45.
-- source:
--   candidate-decomposition:220d8944-f802-44d2-966d-fe70c0b837f8:deeb0988f6eb99b823165bfae6db19d2790d451a1af46fa48f3bd2b5b8fd3c45

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_path_stepLength_le_one
import Theorems.Thm_p2m_path_primal_step_contraction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

section
theorem p2m_path_primal_decay {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k)) :
    ∀ k ≤ K, norm1 (primalInfeas A b (s k)) ≤ (1 - t) ^ k * norm1 (primalInfeas A b (s 0)) := by sorry
end
