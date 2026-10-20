-- Prove2me | Theorems.Thm_p2m_complementarity_step
-- name    : p2m_complementarity_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:25:45.780856+00:00
-- url     : https://prove2.me/theorems/634e4bce-cd14-4bf7-8e71-7a758d0a4e00
-- title:
--   p2m_complementarity_step
-- statement:
--   Automatically extracted helper theorem p2m_complementarity_step from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
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

theorem p2m_complementarity_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (M : ℝ) (hx : normInf p.x ≤ M) (hy : normInf p.y ≤ M) :
    complementarity p' ≤
      (1 - (1 - δ) * stepLength r p d) * complementarity p
        + M * norm1 (primalInfeas A b p) + M * norm1 (dualInfeas A c p) := by sorry
