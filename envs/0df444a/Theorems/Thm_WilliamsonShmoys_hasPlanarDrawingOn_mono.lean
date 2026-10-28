-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:26:02.533765+00:00
-- url     : https://prove2.me/theorems/993c1fe5-cb84-4e59-8b82-fb9e3523df6a
-- title:
--   Planarity is preserved by deleting edges
-- statement:
--   If a graph has a crossing-free drawing, every spanning subgraph has a crossing-free drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  sorry
