-- Prove2me | Theorems.Thm_p2m_primal_step_contraction
-- name    : p2m_primal_step_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T16:26:08.104464+00:00
-- url     : https://prove2.me/theorems/869031ff-9557-429b-8f07-c7aed100074a
-- title:
--   p2m_primal_step_contraction
-- statement:
--   Automatically extracted helper theorem p2m_primal_step_contraction from oversized parent candidate 8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648.
-- source:
--   candidate-decomposition:c32d94c0-348c-428c-b709-764f95b9fc8d:8dd656f44d22286e459e436fb88ab1de64c601aa0da72161df7a65c8b57e3648

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
import Theorems.Thm_p2m_primal_update
import Theorems.Thm_p2m_norm1_smul
import Theorems.Thm_p2m_norm1_nonneg
import Theorems.Thm_p2m_stepLength_le_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
open scoped VanderbeiLP.PathFollowing

theorem p2m_primal_step_contraction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (δ r t : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (ht : t ≤ stepLength r p d) :
    norm1 (primalInfeas A b p') ≤ (1 - t) * norm1 (primalInfeas A b p) := by sorry
