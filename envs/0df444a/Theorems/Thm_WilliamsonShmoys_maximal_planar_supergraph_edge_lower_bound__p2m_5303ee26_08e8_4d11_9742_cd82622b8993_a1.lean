-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:01.618361+00:00
-- url     : https://prove2.me/theorems/2034cbed-4d04-4066-8648-bb4c6652a55d
-- title:
--   A maximal drawable graph reaches the planar edge lower bound
-- statement:
--   An inclusion-maximal drawable graph on a finite vertex type with at least three vertices has at least `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    ∃ dN : DecidableRel N.Adj,
      (letI : DecidableRel N.Adj := dN
       3 * Fintype.card V - 6 ≤ N.edgeFinset.card) := by
  sorry
