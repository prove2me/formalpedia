-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- name    : WilliamsonShmoys.finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:15.569478+00:00
-- url     : https://prove2.me/theorems/c7e47ca5-1b04-4237-81ca-6b57f8f3c2cb
-- title:
--   Finite maximality yields a connected extension
-- statement:
--   On a finite vertex type, if every disconnected graph extending G and satisfying Q has a strictly larger extension still satisfying Q, then some connected extension of G satisfies Q. Prove this by maximizing edge-set cardinality among eligible graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_maximal_extension__p2m_1743449e_70b2_453d_82e4_df1f7d1e75bd_a3
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : SimpleGraph V → Prop) (hQ : Q G)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet → Q K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet ∧ Q L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ Q H ∧ H.Connected := by sorry
