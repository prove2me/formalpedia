-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_bound_of_connected_induced_subgraph_bounds
-- name    : WilliamsonShmoys.edge_count_bound_of_connected_induced_subgraph_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:35:27.307319+00:00
-- url     : https://prove2.me/theorems/52a74459-6cee-48c3-921b-7e21e81c1d16
-- title:
--   Assemble edge bounds across connected components
-- statement:
--   If every connected induced subgraph with at least three vertices satisfies its local planar edge bound, then the whole finite simple graph with at least three vertices satisfies the same global bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_bound_of_connected_induced_subgraph_bounds {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hlocal : ∀ (S : Set V), (H.induce S).Connected → 3 ≤ Nat.card S → (H.induce S).edgeSet.ncard + 6 ≤ 3 * Nat.card S) (hcard : 3 ≤ Nat.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
