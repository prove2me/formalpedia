-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- name    : WilliamsonShmoys.planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:41.386761+00:00
-- url     : https://prove2.me/theorems/cf7c4288-a938-4a87-b27f-3fd599c4349b
-- title:
--   Every drawable finite graph has a maximal drawable extension
-- statement:
--   Every drawable finite simple graph is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_maximal_drawable_extension__p2m_df568397_14d2_4b43_b482_47a2ce432eea_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
