-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1
-- name    : WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:07.860912+00:00
-- url     : https://prove2.me/theorems/4b11b1b8-1e17-4a48-8df5-b53a8b34c658
-- title:
--   Maximal extension for a property of finite graphs
-- statement:
--   For any property of graphs on a finite vertex type, every graph satisfying that property has a property-satisfying supergraph that is maximal among property-satisfying supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_property_has_maximal_extension__p2m_b14cb1c9_e46e_498d_93f0_e98be9265b47_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ W : SimpleGraph V, G ≤ W ∧ P W ∧ ∀ H : SimpleGraph V, W ≤ H → P H → H = W := by sorry
