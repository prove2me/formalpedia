-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_edge_monotone
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_edge_monotone
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T02:57:12.648209+00:00
-- url     : https://prove2.me/theorems/703ffaca-f214-4965-936c-28ab496c768f
-- title:
--   Connect components of a planar drawing without losing edges
-- statement:
--   Any finite graph with the supplied crossing-free drawing has a connected planar supergraph on the same vertices whose edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_edge_monotone
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
