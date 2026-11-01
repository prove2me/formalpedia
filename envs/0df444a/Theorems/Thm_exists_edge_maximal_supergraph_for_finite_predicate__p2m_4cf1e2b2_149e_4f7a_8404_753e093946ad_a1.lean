-- Prove2me | Theorems.Thm_exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1
-- name    : exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:23.063236+00:00
-- url     : https://prove2.me/theorems/65140436-7796-4e67-94af-f8777aba181c
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal among predicate-satisfying extensions of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V,
      R N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        R P →
        (∀ u v, M.Adj u v → P.Adj u v) →
        (∀ u v, N.Adj u v → P.Adj u v) →
        P = N) := by sorry
