-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_planar_upper_retry3
-- name    : WilliamsonShmoys.edge_count_planar_upper_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:28:26.381608+00:00
-- url     : https://prove2.me/theorems/10e52420-af8b-466f-a802-c419fe3502f6
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_planar_upper_retry3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
