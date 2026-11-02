-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:31.89578+00:00
-- url     : https://prove2.me/theorems/2525091e-2670-4eeb-ace8-6dcc3f97c45d
-- title:
--   Finite choice of a maximal graph satisfying a property
-- statement:
--   For a finite ordered vertex type, any graph P satisfying a property Q has a Q-satisfying supergraph that is inclusion maximal among Q-satisfying supergraphs of P.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_by_finite_choice__p2m_8945f9a8_f1f1_4069_b3b7_48c3e7c6f526_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (Q : SimpleGraph V → Prop)
    (hP : Q P) :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      Q H ∧
      (∀ K : SimpleGraph V, Q K → H ≤ K → K ≤ H) := by sorry
