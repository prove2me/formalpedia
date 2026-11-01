-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- name    : WilliamsonShmoys.planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:10.240762+00:00
-- url     : https://prove2.me/theorems/b857a82c-8bba-4f53-a10b-55c8fcca96a0
-- title:
--   Finite edge-maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_completion__p2m_aaf33811_225e_424c_a7fa_7688f68b512b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
