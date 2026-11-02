-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- name    : WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:42:52.724033+00:00
-- url     : https://prove2.me/theorems/15adcf76-f3b0-4eb0-a8d6-6562dc150ecb
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on at least three vertices has exactly 3|V| − 6 edges. The n = 3 case is included; maximality forces the graph to be K₃.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_edge_count__p2m_724aac7b_31c9_4291_9b6d_4edefcb29b4d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
