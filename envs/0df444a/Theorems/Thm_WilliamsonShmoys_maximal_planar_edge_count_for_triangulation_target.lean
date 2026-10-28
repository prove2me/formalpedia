-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_target
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:33:42.71175+00:00
-- url     : https://prove2.me/theorems/dbdacf25-a7b5-4018-9ce6-767cceb6de44
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A graph with a drawing as defined by `HasPlanarDrawingOn`, maximal among planar supergraphs on the same vertex type, has exactly 3n−6 edges when its finite vertex type has at least three elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_target
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
