-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_drawing_32fad0ec
-- name    : WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_32fad0ec
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:00:06.985975+00:00
-- url     : https://prove2.me/theorems/902ae8a0-c285-47b0-b405-17f0b653d601
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A simple graph with the specified planar drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_for_maximal_drawing_32fad0ec
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
