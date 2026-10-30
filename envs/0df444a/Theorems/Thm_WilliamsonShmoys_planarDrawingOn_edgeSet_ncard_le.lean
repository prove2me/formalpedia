-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_edgeSet_ncard_le
-- name    : WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:51:19.731309+00:00
-- url     : https://prove2.me/theorems/133db091-c1c2-4386-b30f-a30d09214462
-- title:
--   Planar edge count upper bound
-- statement:
--   A finite simple graph on at least three vertices with the given crossing-free drawing has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawingOn_edgeSet_ncard_le
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
