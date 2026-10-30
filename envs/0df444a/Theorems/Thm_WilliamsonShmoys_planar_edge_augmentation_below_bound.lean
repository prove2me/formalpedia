-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:24:25.013576+00:00
-- url     : https://prove2.me/theorems/a11205c3-51bf-4409-a8f2-455e7e17d8d2
-- title:
--   Augment a planar graph below the triangulation bound
-- statement:
--   A finite simple planar graph on at least three vertices with fewer than 3n−6 edges has a planar strict supergraph on the same vertex set, witnessed by at least one newly added edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, K.Adj u v ∧ ¬ G.Adj u v := by sorry
