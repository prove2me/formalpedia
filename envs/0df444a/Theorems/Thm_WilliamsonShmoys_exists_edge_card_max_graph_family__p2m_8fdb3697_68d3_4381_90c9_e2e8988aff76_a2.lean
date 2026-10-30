-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- name    : WilliamsonShmoys.exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:39.695366+00:00
-- url     : https://prove2.me/theorems/80d4a099-349d-41af-9d0f-fcca3d96c4ed
-- title:
--   A graph family has a member with maximum edge count
-- statement:
--   Every nonempty family of simple graphs on a finite vertex type has a member with at least as many edges as every other family member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_card_max_graph_family__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
    {V : Type} [Fintype V]
    (S : SimpleGraph V → Prop) (hS : ∃ G, S G) :
    ∃ M, S M ∧ ∀ N, S N → Set.ncard M.edgeSet ≥ Set.ncard N.edgeSet := by sorry
