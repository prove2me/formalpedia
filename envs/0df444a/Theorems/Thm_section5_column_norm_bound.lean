-- Prove2me | Theorems.Thm_section5_column_norm_bound
-- name    : section5_column_norm_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:25.268803+00:00
-- url     : https://prove2.me/theorems/8cd77288-3c59-4688-a61e-f8ed09bb0e48
-- title:
--   Operator action bounded by a maximal column
-- statement:
--   Let $A:\mathbb C^n\to\mathbb C^n$ be a continuous complex linear operator, and write $e_i$ for the standard coordinate vectors. Suppose $j$ indexes a column of maximal norm: $\|Ae_i\|\le\|Ae_j\|$ for all $i$. For every unit vector $v$,
--
--   $$
--   \|Av\|\le n\|Ae_j\|.
--   $$
--
--   This relates the action on an arbitrary unit vector to a selected maximal column.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5PowerColumnRecovery.lean, section5_column_norm_bound, lines 16–36.

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_column_norm_bound {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (j : Fin n) (hmax : ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1) :
    ‖A v‖ ≤ n*‖A (section5_coordinate_ket j)‖ := by sorry
