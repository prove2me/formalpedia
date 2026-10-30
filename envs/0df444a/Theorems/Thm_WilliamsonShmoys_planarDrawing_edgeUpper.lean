-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edgeUpper
-- name    : WilliamsonShmoys.planarDrawing_edgeUpper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:07:29.403995+00:00
-- url     : https://prove2.me/theorems/18304977-637a-4fac-9dc5-be6b4c033919
-- title:
--   Simple planar edge upper bound from a drawing
-- statement:
--   A simple graph on at least three vertices with the supplied crossing-free drawing has at most 3V−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planarDrawing_edgeUpper
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
