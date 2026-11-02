-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:01.796689+00:00
-- url     : https://prove2.me/theorems/75eb6681-dffa-41bf-ba37-6fc423d4fd9b
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most 3|V| − 6 edges, stated without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
