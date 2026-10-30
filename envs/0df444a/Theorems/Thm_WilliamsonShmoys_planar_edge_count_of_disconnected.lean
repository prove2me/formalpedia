-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_disconnected
-- name    : WilliamsonShmoys.planar_edge_count_of_disconnected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:07:43.417155+00:00
-- url     : https://prove2.me/theorems/03529993-0cac-4c04-9322-56ef094f9836
-- title:
--   Planar edge bound for disconnected graphs
-- statement:
--   A disconnected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. Restrict the drawing to each connected component. Components of size at least three satisfy the connected planar estimate; components of size one or two satisfy the elementary bounds from simplicity. Count each edge in its unique component and sum. Since there are at least two nonempty components, the componentwise losses give the required total allowance of six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_of_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdisconn : ¬ G.Connected) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
