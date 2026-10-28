-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_edge_count_monotone
-- name    : WilliamsonShmoys.edge_bound_edge_count_monotone
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:58:52.269186+00:00
-- url     : https://prove2.me/theorems/8f5f308d-e2d7-4b78-899e-c560c77ed57c
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   For simple graphs on the same finite vertex type, inclusion of graphs implies inclusion of their edge sets and hence monotonicity of edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_edge_count_monotone
    {V : Type} [Fintype V]
    {G H : SimpleGraph V}
    (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
