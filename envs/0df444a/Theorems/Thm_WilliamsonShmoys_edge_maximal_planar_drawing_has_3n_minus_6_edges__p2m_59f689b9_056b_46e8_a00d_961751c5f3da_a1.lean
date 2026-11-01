-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:03.098095+00:00
-- url     : https://prove2.me/theorems/64226b9d-e479-429e-9ec8-cb1b67946ff3
-- title:
--   Edge maximal planar graphs have the triangulation edge count
-- statement:
--   An edge maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. A proof route is to use the drawing to obtain a plane embedding, show maximality forces every face to be a triangle, and apply Euler’s formula. The cases |V|=3 and |V|=4 give counts 3 and 6, respectively.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      letI : DecidableRel U.Adj := dU
      letI : DecidableRel W.Adj := dW
      HasPlanarDrawingOn W →
      U.edgeFinset ⊆ W.edgeFinset →
      W.edgeFinset = U.edgeFinset) :
    letI : DecidableRel U.Adj := dU
    U.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
