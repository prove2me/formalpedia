-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:41.813822+00:00
-- url     : https://prove2.me/theorems/ea362c92-0899-4173-a9a5-a6ca062e0269
-- title:
--   Every drawable graph extends to a triangulation
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every graph with a crossing-free drawing has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. This is a triangulation-extension result, and it does not assume the input graph is maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_fba5509b_7521_41eb_ae0d_1c68b4ac0c26_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
