-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected
-- name    : WilliamsonShmoys.planar_edge_count_of_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:06:27.669412+00:00
-- url     : https://prove2.me/theorems/cd5dc03f-4687-45dc-a860-d03b2220ba17
-- title:
--   Planar edge bound for connected graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler-formula core: derive the face count for a connected embedding, count incidences of edges with faces, and use that a simple plane graph with at least three vertices has face boundary length at least three, treating bridge incidences in the usual way.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_of_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
