-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a4
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a4
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T07:33:30.574993+00:00
-- url     : https://prove2.me/theorems/37f7f53d-fcc4-438f-a336-4b0c6957a350
-- title:
--   Maximal drawable supergraph on a fixed vertex set
-- statement:
--   Among the finitely many simple graphs on the same vertex type that contain L and admit a drawing, one has maximum edge count and is maximal among drawable supergraphs of L. Its edge count is at least that of L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, L ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) ∧
      L.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
