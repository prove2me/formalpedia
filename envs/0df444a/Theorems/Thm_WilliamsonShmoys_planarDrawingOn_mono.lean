-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono
-- name    : WilliamsonShmoys.planarDrawingOn_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:10:49.877887+00:00
-- url     : https://prove2.me/theorems/09b60d69-96a4-4468-a6c0-3c3044c1169d
-- title:
--   Planar drawings pass to subgraphs
-- statement:
--   If H has a crossing-free drawing and G is a subgraph of H on the same ordered vertex type, then G has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_mono {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) : WilliamsonShmoys.HasPlanarDrawingOn H → WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
