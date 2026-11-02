-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:38:36.070817+00:00
-- url     : https://prove2.me/theorems/0fdd9833-169b-4602-b2ca-e98b4dc37310
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_71bf5396_ae49_4e3b_9478_7acac339f298_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 <= Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧
      (letI : DecidableRel U.Adj := Classical.decRel U.Adj
       3 * Fintype.card V = U.edgeFinset.card + 6) := by sorry
