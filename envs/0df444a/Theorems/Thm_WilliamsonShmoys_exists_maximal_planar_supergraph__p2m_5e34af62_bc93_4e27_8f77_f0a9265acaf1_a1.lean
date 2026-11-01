-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:49.149256+00:00
-- url     : https://prove2.me/theorems/62c66bf3-533d-43c1-bde3-37ac00c5d3e8
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5e34af62_bc93_4e27_8f77_f0a9265acaf1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) := by sorry
