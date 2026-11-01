-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- name    : WilliamsonShmoys.edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:51.26361+00:00
-- url     : https://prove2.me/theorems/e48a1408-aa0e-492f-adb9-2acab06f5494
-- title:
--   Transfer an edge bound from a supergraph
-- statement:
--   This new combinatorial lemma removes the edge-count transfer from the parent. The subgraph relation gives inclusion of edge finsets, so cardinality monotonicity transfers the supergraph bound directly. It needs no vertex-count hypothesis beyond the bound itself.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_subgraph_bound__p2m_52ae77ae_f85b_40f5_bd03_34373df951b6_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hKH : K ≤ H)
    (hHbound : H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
