-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:36:48.677691+00:00
-- url     : https://prove2.me/theorems/89ca6453-1971-4f8a-b52b-11a113611db9
-- title:
--   Extend a drawable finite graph to an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal under drawable supergraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_maximal__p2m_2266ad6e_a873_4db0_8a1d_ced08babaea4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hplanar : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G.edgeSet ⊆ L.edgeSet ∧
      HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K.edgeSet = L.edgeSet := by sorry
