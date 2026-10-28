-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exact_edge_count_completion_b82980ee
-- name    : WilliamsonShmoys.planar_drawing_exact_edge_count_completion_b82980ee
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:24:50.308476+00:00
-- url     : https://prove2.me/theorems/65129707-b6d0-4954-b2a6-86f8d9448780
-- title:
--   Exact edge-count completion of a planar drawing
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices with exactly 3n − 6 edges. The three-vertex case is the triangle. In general, extend the drawing to a maximal planar graph; its faces are triangular, and Euler’s formula gives the edge count. Establishing this completion and count for the formal drawing predicate is the core geometric obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exact_edge_count_completion_b82980ee
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
