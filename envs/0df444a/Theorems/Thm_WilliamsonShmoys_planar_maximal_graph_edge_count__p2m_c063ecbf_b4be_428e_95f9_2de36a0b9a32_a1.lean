-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
-- name    : WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T23:06:43.42717+00:00
-- url     : https://prove2.me/theorems/ec284709-a18f-4c8c-aa4a-41fee9be8d7b
-- title:
--   Count the edges of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_graph_edge_count__p2m_c063ecbf_b4be_428e_95f9_2de36a0b9a32_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
