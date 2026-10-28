-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_54a0e51c_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.planar_edge_augmentation_54a0e51c_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:39:27.781255+00:00
-- url     : https://prove2.me/theorems/8460384a-9cb9-4641-9067-a05bdb77e75d
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that is maximal under edge inclusion among drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_54a0e51c_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V,
      G.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ H : SimpleGraph V,
        N.edgeSet ⊆ H.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H.edgeSet ⊆ N.edgeSet := by sorry
