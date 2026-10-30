-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_single_edge_augmentation_c61b3391
-- name    : WilliamsonShmoys.planar_single_edge_augmentation_c61b3391
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:01:28.066087+00:00
-- url     : https://prove2.me/theorems/55b4dccf-4d10-44b5-877b-8055cea99126
-- title:
--   Add one edge below the maximal planar count
-- statement:
--   If a finite simple graph on at least three vertices has a crossing-free drawing and fewer than three times its vertex count minus six edges, it has a crossing-free supergraph on the same vertices with exactly one additional edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_single_edge_augmentation_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard = G.edgeSet.ncard + 1 := by sorry
