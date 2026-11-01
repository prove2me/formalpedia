-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
-- name    : WilliamsonShmoys.planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:21.717743+00:00
-- url     : https://prove2.me/theorems/8878012f-4621-4e20-8c97-e8aa106c5519
-- title:
--   Sparse drawable graphs admit a strict planar extension
-- statement:
--   A drawable simple graph on at least three fixed vertices whose edge count is strictly below 3|U|−6 admits a strict supergraph on those vertices that also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_sparse_extension__p2m_5770b3e4_2ec8_40d1_b3e9_07b1ee561228_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hsparse : K.edgeSet.ncard < 3 * Fintype.card U - 6) :
    ∃ L : SimpleGraph U, K ≤ L ∧ K ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
