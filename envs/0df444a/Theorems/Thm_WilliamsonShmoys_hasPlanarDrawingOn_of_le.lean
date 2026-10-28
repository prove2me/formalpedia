-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_of_le
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_of_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:37:04.226257+00:00
-- url     : https://prove2.me/theorems/e997597f-15d6-4121-b705-da72d71f2f18
-- title:
--   Planar drawing is inherited by subgraphs
-- statement:
--   If a graph is a subgraph of a graph with a crossing-free drawing, it has a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_of_le
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
