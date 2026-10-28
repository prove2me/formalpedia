-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_nat_edge_count_completion
-- name    : WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:03:24.221235+00:00
-- url     : https://prove2.me/theorems/553ae5ef-795b-4437-a258-dbe91f157b7c
-- title:
--   A drawable graph has a maximal-edge drawable completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly 3|V| − 6. For three vertices, complete to the triangle; otherwise extend the drawing to a triangulation and count edges using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_nat_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
