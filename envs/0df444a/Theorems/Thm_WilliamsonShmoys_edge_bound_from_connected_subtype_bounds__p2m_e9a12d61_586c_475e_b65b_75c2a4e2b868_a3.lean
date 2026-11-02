-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_connected_subtype_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
-- name    : WilliamsonShmoys_edge_bound_from_connected_subtype_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:36:54.871214+00:00
-- url     : https://prove2.me/theorems/9b15412f-e265-42ce-9016-abfc489359e7
-- title:
--   Combine edge bounds over connected induced subgraphs
-- statement:
--   If every connected induced graph on a subtype of at least three vertices satisfies the 3n−6 edge bound, then the whole finite simple graph with at least three vertices satisfies it. The proof partitions vertices into connected components, bounds components of size one or two directly, and sums the bounds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_edge_bound_from_connected_subtype_bounds__p2m_e9a12d61_586c_475e_b65b_75c2a4e2b868_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 ≤ s.card →
      (L.induce (fun v : V => v ∈ s)).Connected →
      (L.induce (fun v : V => v ∈ s)).edgeSet.ncard ≤ 3 * s.card - 6) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
