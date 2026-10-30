-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:54:13.880195+00:00
-- url     : https://prove2.me/theorems/2907dc87-c05a-4d84-a687-2b7bae17f05a
-- title:
--   Edge bound for every graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that has the given crossing-free drawing has at most 3|V|−6 edges; maximality among drawable supergraphs is not required.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
