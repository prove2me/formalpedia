-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_saturated_edge_bound
-- name    : WilliamsonShmoys.planarDrawing_saturated_edge_bound
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T04:27:02.010334+00:00
-- url     : https://prove2.me/theorems/87d158d3-789b-435d-a7d0-4ef09f3e1568
-- title:
--   Edge bound for a saturated planar drawing
-- statement:
--   A drawable simple graph on at least three vertices whose edge count cannot be increased by passing to a drawable supergraph has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_saturated_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q →
      P.edgeSet.ncard ≤ Q.edgeSet.ncard) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by sorry
