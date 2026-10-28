-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_from_drawing
-- name    : WilliamsonShmoys.planar_simple_edge_bound_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:51:53.588147+00:00
-- url     : https://prove2.me/theorems/3c94c84b-b9b0-426b-a463-ed050367b9c9
-- title:
--   Edge bound for a finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
