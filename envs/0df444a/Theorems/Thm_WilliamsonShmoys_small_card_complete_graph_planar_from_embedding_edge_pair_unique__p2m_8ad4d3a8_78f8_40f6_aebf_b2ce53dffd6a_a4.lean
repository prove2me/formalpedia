-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- name    : WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:51.691795+00:00
-- url     : https://prove2.me/theorems/82b09990-ed85-405d-9d4a-e61dc0e488ae
-- title:
--   There are no two distinct increasing edges
-- statement:
--   A finite linearly ordered type with fewer than three elements cannot contain two distinct strictly increasing ordered vertex pairs. This makes the parent’s condition on intersections between distinct edges vacuous. Prove it by showing that two distinct increasing pairs require at least three distinct vertices (equivalently, by a finite-cardinality argument); the parent obtains `False` from this child before needing any additional facts about the arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_edge_pair_unique__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (hsmall : Fintype.card V < 3) (u v x y : V)
    (huv : u < v) (hxy : x < y) (hne : Not ((u, v) = (x, y))) :
    False := by
  sorry
