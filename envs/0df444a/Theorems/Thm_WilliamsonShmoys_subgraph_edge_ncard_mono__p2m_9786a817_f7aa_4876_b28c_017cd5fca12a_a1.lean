-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- name    : WilliamsonShmoys.subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:44.316395+00:00
-- url     : https://prove2.me/theorems/73c2214e-c2f5-4b78-9a71-472bc209e201
-- title:
--   Monotonicity of edge-set cardinality under subgraphs
-- statement:
--   For finite-vertex simple graphs, inclusion as a subgraph implies that the edge-set cardinality of the smaller graph is at most that of the larger graph. Prove by edge-set inclusion and finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.subgraph_edge_ncard_mono__p2m_9786a817_f7aa_4876_b28c_017cd5fca12a_a1 {V : Type} [Fintype V] (G K : SimpleGraph V) (h : G ≤ K) : G.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
