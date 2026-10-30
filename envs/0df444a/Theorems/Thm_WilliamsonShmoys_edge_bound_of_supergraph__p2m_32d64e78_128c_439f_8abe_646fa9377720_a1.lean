-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- name    : WilliamsonShmoys.edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:05:27.481991+00:00
-- url     : https://prove2.me/theorems/50b2c810-e4c8-40a3-b127-f05af03e8f01
-- title:
--   Transfer an edge bound from a supergraph
-- statement:
--   If one finite graph is a subgraph of another on the same vertex type, any upper bound of the stated form for the supergraph also holds for the subgraph. Prove this by monotonicity of finite edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_supergraph__p2m_32d64e78_128c_439f_8abe_646fa9377720_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hK : K.edgeSet.ncard + 6 <= 3 * Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
