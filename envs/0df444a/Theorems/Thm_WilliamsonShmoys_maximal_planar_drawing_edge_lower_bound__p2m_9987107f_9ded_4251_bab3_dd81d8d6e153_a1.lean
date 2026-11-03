-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:53:57.193193+00:00
-- url     : https://prove2.me/theorems/ceac07bf-1e4c-4add-b38a-2aeb9fce6a2e
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   Every maximal graph on at least three vertices satisfying HasPlanarDrawingOn has at least 3|V| − 6 edges. The geometric and combinatorial work is to use maximality to establish the required connected, triangular facial structure of the embedding, then apply Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_9987107f_9ded_4251_bab3_dd81d8d6e153_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N <= K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by
  sorry
