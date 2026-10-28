-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_54a0e51c
-- name    : WilliamsonShmoys.planar_edge_augmentation_54a0e51c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:16:45.069229+00:00
-- url     : https://prove2.me/theorems/b9fb0b76-2f7c-406a-a3b6-5ba43a0bd005
-- title:
--   Augmenting a drawable graph below the triangulation bound
-- statement:
--   A drawable graph on at least three vertices with fewer than 3n − 6 edges has a strict drawable edge supergraph on the same vertex set. A proof route is to extend the finite planar embedding to a maximal planar embedding while retaining its vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcount : G.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ N : SimpleGraph V,
      G.edgeSet ⊆ N.edgeSet ∧
      ¬ N.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N := by sorry
