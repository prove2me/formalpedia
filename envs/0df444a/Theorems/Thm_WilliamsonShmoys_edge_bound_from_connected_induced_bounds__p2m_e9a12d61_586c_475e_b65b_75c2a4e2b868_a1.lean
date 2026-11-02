-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_induced_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a1
-- name    : WilliamsonShmoys_edge_bound_from_connected_induced_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:43.036724+00:00
-- url     : https://prove2.me/theorems/d473c831-8af1-4c7c-8aaf-c91f919ae3cf
-- title:
--   Combine edge bounds over connected components
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the 3n−6 edge bound, then the entire finite simple graph with at least three vertices satisfies it. The proof partitions into connected components and handles components of sizes one and two directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_edge_bound_from_connected_induced_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 ≤ s.card →
      (L.induce (fun v => v ∈ s)).Connected →
      (L.induce (fun v => v ∈ s)).edgeSet.ncard ≤ 3 * s.card - 6) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
