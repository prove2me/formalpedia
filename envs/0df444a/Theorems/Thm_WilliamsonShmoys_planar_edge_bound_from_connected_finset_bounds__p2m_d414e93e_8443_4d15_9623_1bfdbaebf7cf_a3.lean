-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- name    : WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:19:48.604096+00:00
-- url     : https://prove2.me/theorems/2aff762d-92be-4091-96b6-7b0d6e06700b
-- title:
--   Assemble connected induced-subgraph edge bounds
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the six-slack edge bound, then the whole graph does. Prove this by partitioning into connected components and summing their edge counts. Components of size one contribute no edges; components of size two contribute at most one. Components of size at least three contribute the stated six-unit slack. When all components are small, the total-size hypothesis and the same small-component estimates provide at least six units of slack. This removes disconnected-component bookkeeping from the connected planar argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_connected_finset_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomponents : ∀ (W : Finset V), 3 ≤ W.card →
      (M.induce (W : Set V)).Connected →
      (M.induce (W : Set V)).edgeSet.ncard + 6 ≤ 3 * W.card) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
