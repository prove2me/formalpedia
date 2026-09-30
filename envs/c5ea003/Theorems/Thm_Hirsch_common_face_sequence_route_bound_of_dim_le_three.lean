-- Prove2me | Theorems.Thm_Hirsch_common_face_sequence_route_bound_of_dim_le_three
-- name    : Hirsch.common_face_sequence_route_bound_of_dim_le_three
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T01:55:19.574085+00:00
-- url     : https://prove2.me/theorems/f6de5471-1203-47f6-af99-72bb5fa89e2c
-- title:
--   Low-dimensional common-face sequences have linear graph routes
-- statement:
--   A feasible checkpoint sequence whose consecutive common faces have dimension at most three admits a padded graph route of length $nL$.
--
--   Let $P\subseteq\mathbb{R}^d$ be a bounded $n$-row H-polytope, and let $w_0,\dots,w_L$ be feasible points of $P$ with $w_0$ and $w_L$ vertices. If every consecutive pair has common-face dimension $h\le 3$, then there is a padded vertex-edge walk of $P$ from $w_0$ to $w_L$ of length $nL$. Intermediate checkpoints need not be vertices.
--
--   The argument supplies each consecutive common face with Klee's budget $n-h\le n$, then applies the already proved feasible-face-cover routing theorem. This does not bound sequences that contain a consecutive pair of common-face dimension four or more.
--
--   **Formalization Note** Walks are padded. The budget $nL$ uses the original number of inequalities, not an irredundant facet count.
-- source:
--   Composition of Prove2Me theorems Hirsch.common_face_diameter_of_dim_le_three (Klee in common-face coordinates) and Hirsch.feasible_face_covered_sequence_route_bound (face-preserving checkpoint routing). No literature-priority claim.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_sequence_route_bound_of_dim_le_three
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ Set.extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ Set.extremePoints ℝ (Hpoly a b))
    (hdim : ∀ k < L,
      HirschCommonFace.commonFaceDim a b (w k) (w (k + 1)) ≤ 3) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (n * L) = w L ∧
      ∀ r < n * L,
        q r = q (r + 1) ∨ Adj (Hpoly a b) (q r) (q (r + 1)) := by sorry

end Hirsch
