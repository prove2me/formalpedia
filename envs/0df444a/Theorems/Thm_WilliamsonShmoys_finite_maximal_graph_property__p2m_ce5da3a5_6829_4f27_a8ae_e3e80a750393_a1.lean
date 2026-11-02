-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
-- name    : WilliamsonShmoys.finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:45.893082+00:00
-- url     : https://prove2.me/theorems/7cfc2f59-1eb5-4a72-9798-768dc70407c7
-- title:
--   Finite maximality for graph properties
-- statement:
--   For graphs on a finite linearly ordered vertex type, any graph property holding of L has an inclusion-maximal satisfying extension of L. The proof route is finite maximization by edge-set cardinality; the lemma handles empty vertex types as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_graph_property__p2m_ce5da3a5_6829_4f27_a8ae_e3e80a750393_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (Q : SimpleGraph V → Prop) (hQ : Q L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ Q M ∧
      ∀ N : SimpleGraph V, M ≤ N → Q N → N = M := by sorry
