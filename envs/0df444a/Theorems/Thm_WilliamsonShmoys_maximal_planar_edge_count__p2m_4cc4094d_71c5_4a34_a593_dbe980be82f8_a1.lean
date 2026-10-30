-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:59.501351+00:00
-- url     : https://prove2.me/theorems/f1bb3fc5-14ed-4f61-8573-9a7a487e7a06
-- title:
--   A maximal planar graph has the triangulation edge count
-- statement:
--   A maximal simple planar graph on at least three vertices has exactly 3|V|−6 edges. Establish connectivity and triangular faces from maximality for the given drawing notion, then apply Euler’s formula. The lower bound includes the three-vertex case; fewer vertices would invalidate the edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4cc4094d_71c5_4a34_a593_dbe980be82f8_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) : 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
