-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- name    : WilliamsonShmoys.edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:47.792652+00:00
-- url     : https://prove2.me/theorems/0e015a68-0315-4b5b-b751-170f9b92cf9b
-- title:
--   Edge count is monotone under simple-graph containment
-- statement:
--   For finite simple graphs on the same vertex type, containment of adjacency relations implies that the smaller graph has no more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_monotone__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
    {V : Type} [Fintype V]
    (L H : SimpleGraph V) (hLH : L ≤ H) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    L.edgeFinset.card ≤ H.edgeFinset.card := by sorry
