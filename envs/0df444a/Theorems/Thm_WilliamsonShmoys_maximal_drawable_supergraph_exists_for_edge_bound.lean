-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists_for_edge_bound
-- name    : WilliamsonShmoys.maximal_drawable_supergraph_exists_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:31:57.960747+00:00
-- url     : https://prove2.me/theorems/62310638-3484-47fc-93ab-d0f9d925c6d5
-- title:
--   Finite maximal drawable supergraph for edge bounds
-- statement:
--   Every drawable finite graph is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph_exists_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = H.edgeSet := by sorry
