-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- name    : WilliamsonShmoys.finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:54.772283+00:00
-- url     : https://prove2.me/theorems/6589fa02-37e2-48f2-abf0-d80cd3574afc
-- title:
--   Finite strict extension property yields a connected member
-- statement:
--   On a finite vertex type, if the starting graph satisfies a predicate and each disconnected graph satisfying that predicate has a strict extension satisfying it, then there is a connected extension of the starting graph satisfying the predicate. Prove this by choosing a maximal predicate-satisfying extension among the finitely many graphs on the vertex type; the strict-extension hypothesis contradicts disconnectedness of a maximal choice. This removes the finite termination and maximality argument from the parent. The parent supplies the planar predicate and the geometric extension step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_has_connected_member__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ G' : SimpleGraph V, G < G' ∧ P G') :
    ∃ G : SimpleGraph V, H ≤ G ∧ G.Connected ∧ P G := by
  sorry
