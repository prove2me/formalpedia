-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_subgraph_c7059b55_ff77_4f00_a57a_8983712db7a5
-- name    : WilliamsonShmoys.edge_count_mono_of_subgraph_c7059b55_ff77_4f00_a57a_8983712db7a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:51:24.055997+00:00
-- url     : https://prove2.me/theorems/d5ae12a7-b4b7-4635-9100-17a310b94757
-- title:
--   Edge-count monotonicity under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_of_subgraph_c7059b55_ff77_4f00_a57a_8983712db7a5
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hMN : M ≤ N) :
    M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
