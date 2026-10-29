-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:44:11.527997+00:00
-- url     : https://prove2.me/theorems/43679ddc-4676-4da6-9e7a-c2e415931337
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion of adjacency relations implies that the edge-set cardinality is monotone.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_96ae6d88_fda1_42e5_9f5b_cc899dd909d2_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
