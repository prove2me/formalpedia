-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_from_arcs
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_from_arcs
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:20:27.197274+00:00
-- url     : https://prove2.me/theorems/452673b6-6a6d-4d9e-81d5-9b9cfadfe83c
-- title:
--   Arc drawings satisfy the planar edge bound
-- statement:
--   A graph with the supplied crossing-free arc drawing and at least three vertices has at most 3|V|−6 edges. Euler's formula and counting face-boundary lengths provide a proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_from_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
