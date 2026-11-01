-- Prove2me | Theorems.Thm_finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
-- name    : finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:37.251643+00:00
-- url     : https://prove2.me/theorems/2a557de6-cc65-489b-bdd7-b90847ef581b
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph of at least as many edges that is maximal under graph inclusion among predicate-satisfying graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_graph_maximal_extension__p2m_631bc0f5_f3dc_4eb9_811c_fa1521bf437a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      P K ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) → L = K) := by sorry
