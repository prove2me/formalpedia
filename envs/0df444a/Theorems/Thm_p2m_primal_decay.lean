-- Prove2me | Theorems.Thm_p2m_primal_decay
-- name    : p2m_primal_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:44:23.741223+00:00
-- url     : https://prove2.me/theorems/7d0107a9-6e9b-4187-b938-800ac1c4b490
-- title:
--   p2m_primal_decay
-- statement:
--   Automatically extracted helper theorem p2m_primal_decay from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_stepLength_le_one
import Theorems.Thm_p2m_primal_step_contraction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_primal_decay {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k)) :
    ∀ k ≤ K, norm1 (primalInfeas A b (s k)) ≤ (1 - t) ^ k * norm1 (primalInfeas A b (s 0)) := by sorry
