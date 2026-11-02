-- Prove2me | Theorems.Thm_finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- name    : finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:30.758698+00:00
-- url     : https://prove2.me/theorems/79b6d137-d001-4d6b-9dab-c61985bf58de
-- title:
--   A finite graph extension maximizing edge count
-- statement:
--   Every property-satisfying extension family containing K has an extension H whose edge count is at least that of every other property-satisfying extension of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_drawable_edge_count_extension__p2m_4ae5c893_7e52_474c_915d_3ed4ab7c0e94_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       ∀ G : SimpleGraph V,
         letI : DecidableRel G.Adj := Classical.decRel G.Adj
         K ≤ G → P G → G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
