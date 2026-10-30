-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1
-- name    : WilliamsonShmoys.planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:30.421243+00:00
-- url     : https://prove2.me/theorems/d5ea2124-1838-4ceb-a0a8-373ec58ed0bb
-- title:
--   Drawable planar completion with exact edge count
-- statement:
--   Any finite drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertex set with exactly 3n − 6 edges. For three vertices the completion is the triangle; for larger vertex sets the independent proof route is to extend to a maximal planar drawing, establish triangular faces, and count using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_exact_edge_count__p2m_a712b8ac_2693_4359_b1bf_8163c9ce4446_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
