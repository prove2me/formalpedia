-- Prove2me | Theorems.Thm_finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1
-- name    : finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:36.423199+00:00
-- url     : https://prove2.me/theorems/e4c96249-2893-494c-96ec-547253d1cb77
-- title:
--   Finite graph predicates admit maximal extensions
-- statement:
--   For any predicate on graphs over a finite vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal among such supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_graph_maximal_extension__p2m_0d55c294_ea6d_4f9f_a448_4b66814798e5_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, P J → H ≤ J → J = H) ∧
      G.edgeFinset.card ≤ H.edgeFinset.card := by sorry
