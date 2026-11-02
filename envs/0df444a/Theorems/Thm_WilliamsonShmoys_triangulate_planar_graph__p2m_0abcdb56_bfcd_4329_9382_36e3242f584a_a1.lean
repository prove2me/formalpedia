-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1
-- name    : WilliamsonShmoys.triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:51:47.518257+00:00
-- url     : https://prove2.me/theorems/71345845-0812-4936-9e60-f9671145c018
-- title:
--   Triangulated extension of a finite drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the vertex count minus six. The proof should extend the drawing to a triangulation, including when the original graph is disconnected, and count edges using Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
       3 * Fintype.card V = T.edgeFinset.card + 6) := by sorry
