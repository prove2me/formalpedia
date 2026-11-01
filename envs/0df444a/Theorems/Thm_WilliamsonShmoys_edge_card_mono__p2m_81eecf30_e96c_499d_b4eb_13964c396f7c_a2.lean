-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- name    : WilliamsonShmoys.edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:10:24.312707+00:00
-- url     : https://prove2.me/theorems/490def68-2ba9-4159-8d3f-c54931459510
-- title:
--   Monotonicity of edge cardinality
-- statement:
--   For finite graphs on the same vertex type, inclusion of adjacency relations implies that the first graph’s finite edge count is at most the second graph’s edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_mono__p2m_81eecf30_e96c_499d_b4eb_13964c396f7c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    letI : DecidableRel G.Adj := Classical.decRel _
    letI : DecidableRel H.Adj := Classical.decRel _
    G.edgeFinset.card ≤ H.edgeSet.ncard := by sorry
