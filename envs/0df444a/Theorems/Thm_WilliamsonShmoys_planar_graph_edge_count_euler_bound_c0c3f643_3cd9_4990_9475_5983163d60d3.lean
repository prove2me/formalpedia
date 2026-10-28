-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3
-- name    : WilliamsonShmoys.planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T04:49:21.742031+00:00
-- url     : https://prove2.me/theorems/380ac812-3a07-474c-bc2e-8cea054cfda4
-- title:
--   Euler edge bound for finite graphs with a planar drawing
-- statement:
--   Every finite simple graph on at least three vertices whose edges have a drawing satisfying HasPlanarDrawingOn obeys the classical planar edge bound. This generalizes the target by dropping its edge-maximality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_count_euler_bound_c0c3f643_3cd9_4990_9475_5983163d60d3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
