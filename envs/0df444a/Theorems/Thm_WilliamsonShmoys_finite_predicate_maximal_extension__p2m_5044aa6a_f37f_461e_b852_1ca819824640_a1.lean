-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1
-- name    : WilliamsonShmoys.finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:49.415863+00:00
-- url     : https://prove2.me/theorems/781dd872-d82b-41cd-92b7-3c4cf55153dd
-- title:
--   Maximal extension for a predicate on finite-vertex graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal among satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_maximal_extension__p2m_5044aa6a_f37f_461e_b852_1ca819824640_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      P N ∧
      ∀ Q : SimpleGraph V, N ≤ Q → P Q → Q = N := by sorry
