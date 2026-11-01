-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:01.202201+00:00
-- url     : https://prove2.me/theorems/2b14c079-901b-4d89-85a0-5d7005f21dc0
-- title:
--   Edge-maximal planar graph edge lower bound
-- statement:
--   An edge-maximal graph with a crossing-free drawing and at least three vertices has at least 3|V| − 6 edges. This isolates the maximality argument. A proof route establishes that a maximal planar graph on at least three vertices is connected and every face in a planar embedding is triangular; Euler’s formula and edge-face incidence counting then yield the bound, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      HasPlanarDrawingOn W →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       U.edgeFinset ⊆ W.edgeFinset) →
      (letI : DecidableRel U.Adj := dU
       letI : DecidableRel W.Adj := dW
       W.edgeFinset ⊆ U.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     3 * Fintype.card V - 6 ≤ U.edgeFinset.card) := by sorry
