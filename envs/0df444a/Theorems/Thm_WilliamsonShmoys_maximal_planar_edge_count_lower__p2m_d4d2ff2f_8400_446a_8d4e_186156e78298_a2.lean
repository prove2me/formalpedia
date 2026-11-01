-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:54:56.66728+00:00
-- url     : https://prove2.me/theorems/cb206649-7371-4b65-b6a9-a6e949375fbf
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   A graph maximal among drawable supergraphs on the same finite vertex set, with at least three vertices, has at least 3|V|−6 edges. This removes the maximality and triangulation argument from the parent. A proof route shows that maximality forces a connected triangulation and applies Euler’s formula; the size hypothesis handles the small boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d4d2ff2f_8400_446a_8d4e_186156e78298_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      3 * Fintype.card V - 6 ≤ K.edgeFinset.card) := by sorry
