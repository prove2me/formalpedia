-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_graph_for_property__p2m_469d9da7_7454_4371_9a4f_4cc419f09ed2_a1
-- name    : WilliamsonShmoys.exists_maximal_graph_for_property__p2m_469d9da7_7454_4371_9a4f_4cc419f09ed2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:59:36.975264+00:00
-- url     : https://prove2.me/theorems/97420b11-f483-418f-95ef-fd01a7deccbd
-- title:
--   Finite maximality for a graph property
-- statement:
--   For any property R on simple graphs over a fixed finite linearly ordered vertex type, if M has R, then some R graph containing M has no strictly larger R supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_graph_for_property__p2m_469d9da7_7454_4371_9a4f_4cc419f09ed2_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : R M) : ∃ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet ∧ R N ∧ ∀ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet → R P → P = N := by sorry
