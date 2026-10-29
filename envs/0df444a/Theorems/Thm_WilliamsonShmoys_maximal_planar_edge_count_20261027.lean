-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261027
-- name    : WilliamsonShmoys.maximal_planar_edge_count_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:32:33.460475+00:00
-- url     : https://prove2.me/theorems/95820aed-8041-45f3-9657-629ddab11457
-- title:
--   A maximal drawable simple graph has 3n minus 6 edges
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
