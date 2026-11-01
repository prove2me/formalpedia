-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:47.128199+00:00
-- url     : https://prove2.me/theorems/96980b1a-9f95-4fab-928b-4c57cef78d59
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_4c675a48_b2e7_41d9_8987_0c6f38bd3a34_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N = M := by sorry
