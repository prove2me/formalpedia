-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:15.106102+00:00
-- url     : https://prove2.me/theorems/7e88f44c-59d4-43e4-9143-2eb423cca905
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, a graph satisfying the predicate has a predicate-satisfying supergraph that is maximal by edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_58dc5ab1_94a9_407e_bf9a_7b232f0762ef_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop) (hW : P W) :
    letI : DecidableRel W.Adj := Classical.decRel W.Adj
    ∃ H : SimpleGraph V, P H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       W.edgeFinset ⊆ H.edgeFinset) ∧
      ∀ K : SimpleGraph V, P K →
        (letI : DecidableRel H.Adj := Classical.decRel H.Adj
         letI : DecidableRel K.Adj := Classical.decRel K.Adj
         H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset) := by sorry
