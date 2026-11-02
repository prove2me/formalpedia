-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:16.666789+00:00
-- url     : https://prove2.me/theorems/14b8c227-b724-4de5-85b9-cdf4d661eb0f
-- title:
--   Planar triangulation supergraph with exact edge count
-- statement:
--   Any finite graph with at least three vertices and a crossing-free drawing has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. For three vertices, the completion is the triangle; for larger sets, extend to a maximal planar drawing, whose faces are triangular, and apply Euler's formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_c3bfcc58_a4dc_4360_bb5c_96ba0d9daf33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
        3 * Fintype.card V = P.edgeFinset.card + 6) := by sorry
