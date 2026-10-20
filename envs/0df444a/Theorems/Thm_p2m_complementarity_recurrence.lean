-- Prove2me | Theorems.Thm_p2m_complementarity_recurrence
-- name    : p2m_complementarity_recurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:59:23.238549+00:00
-- url     : https://prove2.me/theorems/8da62f93-8f7b-4797-967c-4a89d1741a6c
-- title:
--   p2m_complementarity_recurrence
-- statement:
--   Automatically extracted helper theorem p2m_complementarity_recurrence from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_primal_decay
import Theorems.Thm_p2m_dual_decay
import Theorems.Thm_p2m_normInf_nonneg
import Theorems.Thm_p2m_complementarity_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_complementarity_recurrence {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t M : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (s d : ℕ → PDPoint m n) (K : ℕ)
    (hstep : ∀ k ≤ K, IsPathFollowingStep A b c δ r (s k) (d k) (s (k + 1)))
    (hθ : ∀ k ≤ K, t ≤ stepLength r (s k) (d k))
    (hx : ∀ k ≤ K, normInf (s k).x ≤ M) (hy : ∀ k ≤ K, normInf (s k).y ≤ M)
    (hone : ∀ k ≤ K,
      complementarity (s (k + 1)) ≤
        (1 - (1 - δ) * stepLength r (s k) (d k)) * complementarity (s k)
          + M * norm1 (primalInfeas A b (s k)) + M * norm1 (dualInfeas A c (s k))) :
    ∀ k, k + 1 ≤ K →
      complementarity (s (k + 1)) ≤
        (1 - t * (1 - δ)) * complementarity (s k)
          + M * (1 - t) ^ k
            * (norm1 (primalInfeas A b (s 0)) + norm1 (dualInfeas A c (s 0))) := by sorry
