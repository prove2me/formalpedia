-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:57:21.277975+00:00
-- url     : https://prove2.me/theorems/f4d7c237-0776-4adb-8bad-5150d3e32462
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Every finite drawable simple graph with at least three vertices has at most 3|V|−6 edges. This is the Euler edge bound; the lower-size hypothesis is retained for its boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
