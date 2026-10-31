-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:56.416006+00:00
-- url     : https://prove2.me/theorems/5ba0acd6-35ab-4946-adf8-e1900a9aaa74
-- title:
--   Finite maximal supergraph for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_ef9f633b_8271_42d9_b073_b93d60169594_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : P H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      P K ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        K.edgeFinset ⊆ L.edgeFinset → P L →
          L.edgeFinset = K.edgeFinset := by
  sorry
