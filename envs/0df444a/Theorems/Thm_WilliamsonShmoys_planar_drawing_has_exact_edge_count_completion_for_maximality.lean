-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_for_maximality
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:10:35.151561+00:00
-- url     : https://prove2.me/theorems/eb48bd77-69db-40f2-b2db-c4e8d2ad0dc2
-- title:
--   Completion of a drawable graph to exact planar edge count
-- statement:
--   Any drawable simple graph on at least three finite ordered vertices is contained in a drawable graph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion_for_maximality
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      N.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
