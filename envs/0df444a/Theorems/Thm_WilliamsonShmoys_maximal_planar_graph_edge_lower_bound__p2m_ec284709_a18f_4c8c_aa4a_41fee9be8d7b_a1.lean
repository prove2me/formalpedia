-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T23:25:49.233291+00:00
-- url     : https://prove2.me/theorems/f78503a9-5416-4ae7-a29c-25625a9bc1b3
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V| − 6 edges. This isolates the maximality argument: show that a missing face diagonal could otherwise be added, forcing every face to be triangular, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_lower_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  sorry
