-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_edge_count_of_maximal_drawable
-- name    : WilliamsonShmoys.triangulation_edge_count_of_maximal_drawable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:45:34.973902+00:00
-- url     : https://prove2.me/theorems/0964174b-5d70-4e5f-b89a-ea62311aea14
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   Every inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This child contains the topological core: establish that maximality forces a triangulation, then count edges by Euler’s formula. For three vertices, maximality makes the graph K₃; for larger orders, the route is to show that a nontriangular face admits a drawable diagonal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_edge_count_of_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ H : SimpleGraph V, U ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
