-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_arcs
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_arcs
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:12:36.806721+00:00
-- url     : https://prove2.me/theorems/bce40739-9345-4213-b60f-77ecc5333c94
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly three times the number of vertices minus six edges. The proof route is to establish the standard maximal-planar triangulation property from the drawing and maximality hypotheses, then use Euler's formula. This supplies the edge-count step in the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
