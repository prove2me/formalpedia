-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:30.791385+00:00
-- url     : https://prove2.me/theorems/d0a96286-d6d0-4f9d-8f16-8ff04549e9c7
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_1341e650_028f_415c_aaf6_59348f49d6ab_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet ⊆ K.edgeSet := by sorry
