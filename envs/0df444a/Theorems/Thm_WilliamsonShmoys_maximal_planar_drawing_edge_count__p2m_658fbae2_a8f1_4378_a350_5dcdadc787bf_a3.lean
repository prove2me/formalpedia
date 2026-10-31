-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:04:23.362443+00:00
-- url     : https://prove2.me/theorems/b3857576-7612-4991-8128-4575dd8808dc
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges. The independent route is to establish that maximality gives a connected plane embedding with triangular faces, then derive the count from Euler’s formula and the fact that each edge borders two face sides. At |V| = 3 this gives the triangle count. Formalizing the embedding, faces, and Euler count is the main remaining obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
