-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices
-- name    : WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:37:34.113548+00:00
-- url     : https://prove2.me/theorems/eb2b08a8-a766-4249-9013-1f35c8739fe7
-- title:
--   Edge bound for a simple planar graph
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
