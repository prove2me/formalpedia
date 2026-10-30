-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:46.668403+00:00
-- url     : https://prove2.me/theorems/a06e74bc-2d14-4a85-b8d6-42f2136549b3
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        Set.Subset M.edgeSet N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        N = M := by sorry
