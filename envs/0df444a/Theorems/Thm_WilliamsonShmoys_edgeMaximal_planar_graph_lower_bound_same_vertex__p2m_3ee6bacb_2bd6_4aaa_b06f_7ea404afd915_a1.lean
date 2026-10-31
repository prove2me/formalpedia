-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
-- name    : WilliamsonShmoys.edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:18.798658+00:00
-- url     : https://prove2.me/theorems/ac618f5b-f1ff-4053-9ae3-bb0fc54b8c70
-- title:
--   Edge lower bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on a finite vertex set of size at least three has at least `3 |V| - 6` edges. The embedding's maximality forces a triangulation, after which Euler's formula gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edgeMaximal_planar_graph_lower_bound_same_vertex__p2m_3ee6bacb_2bd6_4aaa_b06f_7ea404afd915_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  sorry
