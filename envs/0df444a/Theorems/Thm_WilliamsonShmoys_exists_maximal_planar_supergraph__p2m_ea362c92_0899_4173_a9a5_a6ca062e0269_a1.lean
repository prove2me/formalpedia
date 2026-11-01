-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:46.956042+00:00
-- url     : https://prove2.me/theorems/16bca688-573d-44ee-b9cc-afdbc73a2caa
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on the given finite vertex type is contained in a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ea362c92_0899_4173_a9a5_a6ca062e0269_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ K : SimpleGraph V, L ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = L := by sorry
