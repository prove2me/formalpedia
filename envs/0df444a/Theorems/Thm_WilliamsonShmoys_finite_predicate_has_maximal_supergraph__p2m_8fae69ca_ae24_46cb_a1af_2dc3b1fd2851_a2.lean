-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- name    : WilliamsonShmoys.finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:31.052746+00:00
-- url     : https://prove2.me/theorems/4e4238ce-8f3e-4527-8519-c90881202c75
-- title:
--   Finite graphs have maximal predicate supergraphs
-- statement:
--   For any graph property preserved when edges are removed, a graph on a finite ordered vertex type has a supergraph satisfying that property which is maximal among such supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_has_maximal_supergraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hN : P N) (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) : ∃ K : SimpleGraph V, N ≤ K ∧ N.edgeSet.ncard ≤ K.edgeSet.ncard ∧ P K ∧ ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by sorry
