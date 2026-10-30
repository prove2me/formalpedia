-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_ncard_triangulation_job9e56ac28_v2
-- name    : WilliamsonShmoys.maximal_planar_ncard_triangulation_job9e56ac28_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:44:37.228179+00:00
-- url     : https://prove2.me/theorems/4e1da140-2dc1-48aa-a5de-903746e6acda
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing has exactly 3n − 6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_ncard_triangulation_job9e56ac28_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hLmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
