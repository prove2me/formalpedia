-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound
-- name    : WilliamsonShmoys.planar_drawing_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:16:51.058357+00:00
-- url     : https://prove2.me/theorems/1ee57aa5-e998-406b-bad5-710fa94af525
-- title:
--   Simple planar drawing edge-count bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. This is the main topological obligation removed from the parent: turn the given arcs into a planar embedding and use Euler’s formula and edge-side counting. Its boundary hypotheses match the standard simple planar edge bound; in particular, three vertices allow a triangle with equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
