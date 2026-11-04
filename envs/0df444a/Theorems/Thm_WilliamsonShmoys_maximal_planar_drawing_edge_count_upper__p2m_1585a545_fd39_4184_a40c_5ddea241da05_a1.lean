-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:48.118303+00:00
-- url     : https://prove2.me/theorems/e34a2546-c833-4430-ac36-3fbd756a8832
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
