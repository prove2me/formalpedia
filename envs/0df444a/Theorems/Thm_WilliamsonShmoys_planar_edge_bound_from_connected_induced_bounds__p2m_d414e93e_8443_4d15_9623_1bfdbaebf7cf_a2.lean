-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
-- name    : WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:17:20.637002+00:00
-- url     : https://prove2.me/theorems/2628e8ee-b64d-494c-87d3-fdf9e69ea636
-- title:
--   Assemble connected induced-subgraph edge bounds
-- statement:
--   If every connected induced subgraph of size at least three obeys the six-slack edge bound, then the whole graph does. Prove this by partitioning vertices into connected components, summing edge counts with no cross-component edges, and treating components of size one and two directly. Components of size at least three supply six units of slack each; if all components are smaller, the hypothesis that the total vertex count is at least three and the size-two edge bound still give at least six units overall.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_d414e93e_8443_4d15_9623_1bfdbaebf7cf_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hcomponents : ∀ (W : Set V), 3 ≤ Nat.card W →
      (M.induce W).Connected →
      (M.induce W).edgeSet.ncard + 6 ≤ 3 * Nat.card W) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
