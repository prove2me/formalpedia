-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_simpleGraph_of_predicate__p2m_e1448a29_6ed5_4290_9f2f_9b3459d52881_a2
-- name    : WilliamsonShmoys.exists_maximal_simpleGraph_of_predicate__p2m_e1448a29_6ed5_4290_9f2f_9b3459d52881_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:58.44188+00:00
-- url     : https://prove2.me/theorems/e39969f1-e5df-4c18-b93d-7b03c29b78e1
-- title:
--   A maximal finite simple graph satisfying a predicate
-- statement:
--   For a finite vertex type, any simple graph R satisfying a predicate P is contained in a P-satisfying graph S that is maximal under edge inclusion among P-satisfying graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_simpleGraph_of_predicate__p2m_e1448a29_6ed5_4290_9f2f_9b3459d52881_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      (∀ u v, R.Adj u v → S.Adj u v) ∧
      P S ∧
      ∀ T : SimpleGraph V,
        (∀ u v, S.Adj u v → T.Adj u v) →
        P T →
        ∀ u v, T.Adj u v → S.Adj u v := by sorry
