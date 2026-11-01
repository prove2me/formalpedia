-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1
-- name    : WilliamsonShmoys.finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:13.260521+00:00
-- url     : https://prove2.me/theorems/e5f03fa7-7d3a-4076-b5bc-4d425df1ae6c
-- title:
--   Finite graph extensions have a maximal predicate-satisfying member
-- statement:
--   For a finite vertex type, every graph satisfying a predicate has a predicate-satisfying supergraph that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_extension_has_maximal_member__p2m_6589fa02_37e2_48f2_abf0_d80cd3574afc_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H) :
    ∃ M : SimpleGraph V, H ≤ M ∧ P M ∧
      ∀ G' : SimpleGraph V, M < G' → ¬ P G' := by
  sorry
