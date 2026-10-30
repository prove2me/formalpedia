-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- name    : WilliamsonShmoys.planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:46.791068+00:00
-- url     : https://prove2.me/theorems/f129ba31-f328-4589-9d1a-06c0bfdd9301
-- title:
--   Transfer an edge bound to a subgraph
-- statement:
--   If a finite simple graph is a subgraph of another graph on the same vertex type, any upper bound on the larger graph’s edge count also bounds the smaller graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : H.edgeSet.ncard + 6 <= 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
