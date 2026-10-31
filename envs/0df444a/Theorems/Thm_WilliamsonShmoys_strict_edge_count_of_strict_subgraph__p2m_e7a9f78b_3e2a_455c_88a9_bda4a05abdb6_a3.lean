-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- name    : WilliamsonShmoys.strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:23.973096+00:00
-- url     : https://prove2.me/theorems/81e767c7-0eeb-42fc-9571-0b5961c7a6ba
-- title:
--   A proper finite simple graph supergraph has more edges
-- statement:
--   For finite simple graphs on the same vertex type, inclusion together with inequality gives a strict inequality of edge counts. Derive proper inclusion of finite edge sets and apply strict monotonicity of cardinality; equality of edge sets would imply equality of the graphs. This removes the finite counting step from the parent and has no extra size boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.strict_edge_count_of_strict_subgraph__p2m_e7a9f78b_3e2a_455c_88a9_bda4a05abdb6_a3 {V : Type} [Fintype V] (K L : SimpleGraph V) (hKL : K ≤ L) (hne : K ≠ L) : K.edgeSet.ncard < L.edgeSet.ncard := by sorry
