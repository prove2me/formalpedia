-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:05.094797+00:00
-- url     : https://prove2.me/theorems/d87be54e-bfcb-4aba-9277-804ad42ab6ab
-- title:
--   Maximal predicate-satisfying supergraph on a finite vertex type
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if H satisfies the predicate, then H has a predicate-satisfying supergraph that is maximal under edge inclusion among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_1bbb274f_042a_4c5e_8e43_fd05505ca5a4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ K : SimpleGraph V, P K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        (∀ u v, L.Adj u v → K.Adj u v)) := by sorry
