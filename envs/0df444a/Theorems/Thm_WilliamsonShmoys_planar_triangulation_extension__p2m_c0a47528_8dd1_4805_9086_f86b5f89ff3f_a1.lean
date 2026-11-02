-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1
-- name    : WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:57.9272+00:00
-- url     : https://prove2.me/theorems/a74ab9cf-0d81-499a-8717-2a45ea195d9c
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Any crossing-free drawing on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. The existing edges are preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_triangulation_extension__p2m_c0a47528_8dd1_4805_9086_f86b5f89ff3f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
