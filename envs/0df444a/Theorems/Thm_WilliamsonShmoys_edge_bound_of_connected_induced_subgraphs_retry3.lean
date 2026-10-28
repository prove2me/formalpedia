-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_connected_induced_subgraphs_retry3
-- name    : WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:14:40.349068+00:00
-- url     : https://prove2.me/theorems/504349a8-6584-4da4-8d63-f8ab76b6b23f
-- title:
--   Assemble connected-subgraph edge bounds
-- statement:
--   If every connected induced subgraph with at least three vertices satisfies the planar edge bound, then the whole graph on at least three vertices does too. Partition into connected components, use the assumed bound on large components, and handle components of sizes one and two using simplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_connected_induced_subgraphs_retry3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hbound : ∀ (S : Finset V), 3 <= S.card → (H.induce (↑S : Set V)).Connected → (H.induce (↑S : Set V)).edgeSet.ncard + 6 <= 3 * Fintype.card {v // v ∈ S}) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
