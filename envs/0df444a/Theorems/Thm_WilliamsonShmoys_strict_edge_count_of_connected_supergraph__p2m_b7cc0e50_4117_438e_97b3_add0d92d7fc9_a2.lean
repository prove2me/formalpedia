-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- name    : WilliamsonShmoys.strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:31:07.117107+00:00
-- url     : https://prove2.me/theorems/60476c53-757d-4611-89ec-6b8b068795cf
-- title:
--   A connected supergraph of a disconnected graph adds an edge
-- statement:
--   If a finite graph is a subgraph of a connected graph but is itself disconnected, the supergraph has at least one more edge. Prove this by showing the edge-set inclusion is strict and applying finite cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2 {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : H.Connected)
    (hG : ¬ G.Connected) :
    G.edgeSet.ncard + 1 ≤ H.edgeSet.ncard := by sorry
