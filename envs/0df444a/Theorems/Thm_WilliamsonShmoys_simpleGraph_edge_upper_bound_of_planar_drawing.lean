-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edge_upper_bound_of_planar_drawing
-- name    : WilliamsonShmoys.simpleGraph_edge_upper_bound_of_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:12:09.75009+00:00
-- url     : https://prove2.me/theorems/0066810a-e363-4f61-93ee-0b1982239d9f
-- title:
--   Euler edge bound for a finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing in the plane has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edge_upper_bound_of_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
