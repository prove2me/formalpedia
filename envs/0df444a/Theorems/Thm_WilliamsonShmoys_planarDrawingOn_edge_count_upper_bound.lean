-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edge_count_upper_bound
-- name    : WilliamsonShmoys.planarDrawingOn_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:53:29.023904+00:00
-- url     : https://prove2.me/theorems/d02b69d5-3f6d-4db9-bc76-cc7c9d187567
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The independent proof route is Euler’s formula together with the fact that every face has boundary length at least three, with the standard component adjustment for disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
