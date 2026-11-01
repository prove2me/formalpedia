-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:30.693649+00:00
-- url     : https://prove2.me/theorems/bf438c7d-c9b0-4785-be74-e422dc135557
-- title:
--   Finite maximal extension for an edge-deletion-closed graph property
-- statement:
--   For any property of finite simple graphs that is preserved when edges are deleted, every graph with the property has a supergraph with the property that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_maximal_extension__p2m_bdc3b847_9c7d_4952_b797_9d04867ba893_a1
    {V : Type} [Fintype V]
    (Q : SimpleGraph V → Prop)
    (hmono : ∀ ⦃G H : SimpleGraph V⦄, H.edgeSet ⊆ G.edgeSet → Q G → Q H)
    (M : SimpleGraph V)
    (hM : Q M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      Q N ∧
      ∀ P : SimpleGraph V,
        N.edgeSet ⊆ P.edgeSet →
        Q P →
        P.edgeSet = N.edgeSet := by
  sorry
