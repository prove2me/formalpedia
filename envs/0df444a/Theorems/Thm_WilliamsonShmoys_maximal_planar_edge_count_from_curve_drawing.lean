-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_curve_drawing
-- name    : WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:15:49.887914+00:00
-- url     : https://prove2.me/theorems/2eaf8c58-5e8d-4429-8f1f-03b4d9b194b4
-- title:
--   Edge count of a maximal graph with a curve drawing
-- statement:
--   A simple graph with at least three vertices that has a crossing-free curve drawing and is maximal among drawable supergraphs on the same vertex type has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_from_curve_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
