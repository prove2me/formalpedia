-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:41:59.957211+00:00
-- url     : https://prove2.me/theorems/c4b40e40-dbd9-4519-a61b-843dc35bfbb5
-- title:
--   Complete a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertex set whose edge count is exactly 3|V|−6. This is the finite planar triangulation-completion theorem, with the edge count supplied by Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_b1659f81_1f0c_4922_9013_d0dbf115cc22_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry
