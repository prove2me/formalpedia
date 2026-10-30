-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:20:10.648441+00:00
-- url     : https://prove2.me/theorems/8f0c4e79-82ed-4eab-8262-744ee1ed1865
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0fdafab4_3fd6_4759_8b58_e983a7df1ef3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
