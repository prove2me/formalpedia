-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:06.514206+00:00
-- url     : https://prove2.me/theorems/4b11c70d-cbc5-465f-a3db-640a30903358
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For any property of simple graphs on a finite vertex type, a graph satisfying the property has an extension satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property__p2m_c7b07ed7_db7c_450f_a64f_c5e3047d491b_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ L : SimpleGraph V, P L ∧ K ≤ L ∧
      ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by
  sorry
