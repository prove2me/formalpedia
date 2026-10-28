-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edgeCard_graph
-- name    : WilliamsonShmoys.exists_max_edgeCard_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:01:07.489205+00:00
-- url     : https://prove2.me/theorems/6a62d073-4a0e-46be-b570-2c706bd9b8e8
-- title:
--   Maximum edge count in a nonempty family of finite graphs
-- statement:
--   Every nonempty family of simple graphs on a finite vertex type has a member whose edge count is at least that of every other member, given finite edge-set instances for the graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_edgeCard_graph
    {V : Type} [Fintype V]
    (edgeFinite : ∀ G : SimpleGraph V, Fintype G.edgeSet)
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ M : SimpleGraph V,
      P M ∧ ∀ N : SimpleGraph V, P N → N.edgeFinset.card ≤ M.edgeFinset.card := by sorry
