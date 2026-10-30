-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_06232b3e
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_06232b3e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:11:10.756679+00:00
-- url     : https://prove2.me/theorems/2a9dccf6-668c-4d19-9019-ad95792f6898
-- title:
--   Upper bound for the edge count of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has at most 3|V|−6 edges. This removes the target’s upper-bound obligation without using maximality. The independent proof route is to join components by noncrossing edges and apply Euler’s planar edge inequality to the resulting connected drawing; joining components does not change the vertex count. The three-vertex boundary gives an upper bound of three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_06232b3e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
