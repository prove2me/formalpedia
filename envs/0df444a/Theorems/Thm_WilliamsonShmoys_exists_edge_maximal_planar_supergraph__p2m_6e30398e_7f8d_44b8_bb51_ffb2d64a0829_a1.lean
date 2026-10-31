-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:34.903586+00:00
-- url     : https://prove2.me/theorems/fbe039dd-0134-49b2-ac78-235d8da9b20f
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph is contained in a drawable graph on the same vertices that is maximal under adding edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet = M.edgeSet := by sorry
