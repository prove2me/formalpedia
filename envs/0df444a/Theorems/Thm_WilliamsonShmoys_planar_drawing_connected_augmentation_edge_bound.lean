-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:39:34.749281+00:00
-- url     : https://prove2.me/theorems/7ddf173f-f263-4a69-8325-2644e3a05912
-- title:
--   Connect a planar drawing without losing edges
-- statement:
--   Augment the supplied drawing to a connected planar supergraph on the same vertices without decreasing the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
