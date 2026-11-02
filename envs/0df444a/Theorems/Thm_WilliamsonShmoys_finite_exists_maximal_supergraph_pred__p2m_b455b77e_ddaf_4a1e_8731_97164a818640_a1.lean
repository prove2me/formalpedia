-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
-- name    : WilliamsonShmoys.finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:14.44082+00:00
-- url     : https://prove2.me/theorems/c87ea621-8171-472e-808e-cecde2deef11
-- title:
--   Finite maximal extension for a predicate on simple graphs
-- statement:
--   For any finite vertex type and any predicate on its simple graphs, every graph satisfying the predicate is contained in a predicate-satisfying graph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_exists_maximal_supergraph_pred__p2m_b455b77e_ddaf_4a1e_8731_97164a818640_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V) (D : SimpleGraph V → Prop)
    (hP : D P) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      D Q ∧
      (∀ R : SimpleGraph V,
        (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
        D R →
        R = Q) := by sorry
