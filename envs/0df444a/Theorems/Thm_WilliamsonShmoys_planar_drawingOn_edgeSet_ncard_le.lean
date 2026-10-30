-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeSet_ncard_le
-- name    : WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:55:41.608995+00:00
-- url     : https://prove2.me/theorems/b573873b-f1bd-43d0-a808-cfbb4593a75b
-- title:
--   Planar edge-count upper bound
-- statement:
--   A drawable finite simple graph on at least three vertices has at most 3|V|−6 edges, including when it is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawingOn_edgeSet_ncard_le
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
