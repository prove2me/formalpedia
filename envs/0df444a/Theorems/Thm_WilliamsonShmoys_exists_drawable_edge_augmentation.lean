-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_augmentation
-- name    : WilliamsonShmoys.exists_drawable_edge_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:35:49.868146+00:00
-- url     : https://prove2.me/theorems/b5b120c7-6d20-4d88-bc17-a71de5c3565a
-- title:
--   Add an edge below the planar bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than the planar edge bound, one can add exactly one edge while preserving drawability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_edge_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by
  sorry
