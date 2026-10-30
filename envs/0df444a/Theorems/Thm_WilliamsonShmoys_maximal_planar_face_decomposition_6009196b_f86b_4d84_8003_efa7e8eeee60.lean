-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:53:48.268841+00:00
-- url     : https://prove2.me/theorems/8c9e6fef-5d83-4474-8c3d-c1b111bd7dbf
-- title:
--   Euler and triangular-face equations for maximal planar drawings
-- statement:
--   A maximal drawable simple graph with at least three vertices has a face count satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
