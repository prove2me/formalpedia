-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:08.790391+00:00
-- url     : https://prove2.me/theorems/27e53667-a776-4b32-8a84-50a3a7284dfa
-- title:
--   Maximality forces the planar edge-count lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V| − 6 edges, stated without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V ≤
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj
       M.edgeFinset.card) + 6 := by sorry
