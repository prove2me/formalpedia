-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_single_edge_augmentation_below_euler_bound_b54e7d04
-- name    : WilliamsonShmoys.planar_single_edge_augmentation_below_euler_bound_b54e7d04
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:38:35.903985+00:00
-- url     : https://prove2.me/theorems/30a083df-0589-4815-ad36-02507362ad68
-- title:
--   Single-edge planar augmentation below the Euler bound
-- statement:
--   If a graph with a crossing-free drawing on at least three vertices has fewer than `3n − 6` edges, one absent edge can be added while preserving planarity. The strict inequality is essential: no augmentation is claimed at the maximal count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_single_edge_augmentation_below_euler_bound_b54e7d04
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hsmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊂ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
