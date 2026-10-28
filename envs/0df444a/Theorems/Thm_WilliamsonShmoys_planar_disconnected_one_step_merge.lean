-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_one_step_merge
-- name    : WilliamsonShmoys.planar_disconnected_one_step_merge
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T08:18:02.515986+00:00
-- url     : https://prove2.me/theorems/d44ba534-6ff6-4912-ab73-7176a86a9fcd
-- title:
--   Add a planar edge between distinct components
-- statement:
--   Every disconnected finite graph with the specified crossing-free drawing can be enlarged by a strict planar supergraph containing an edge between vertices that were in different connected components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_disconnected_one_step_merge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
