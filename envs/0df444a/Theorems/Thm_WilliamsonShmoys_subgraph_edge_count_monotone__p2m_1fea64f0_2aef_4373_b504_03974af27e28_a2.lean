-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- name    : WilliamsonShmoys.subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:12:29.109598+00:00
-- url     : https://prove2.me/theorems/c14ce536-67ca-4d29-87a3-1b9dbf136830
-- title:
--   Edge count is monotone under subgraph inclusion
-- statement:
--   For finite vertex types, inclusion of simple graphs implies inclusion of their edge sets and hence monotonicity of edge count. This removes the counting step from the parent; a direct proof route is finite-set cardinality monotonicity applied to the edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_count_monotone__p2m_1fea64f0_2aef_4373_b504_03974af27e28_a2 {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) : G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
