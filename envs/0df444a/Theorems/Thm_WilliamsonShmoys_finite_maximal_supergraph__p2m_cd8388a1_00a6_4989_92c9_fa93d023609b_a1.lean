-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:56.767984+00:00
-- url     : https://prove2.me/theorems/8fdb3697-68d3-4381-90c9-e2e8988aff76
-- title:
--   Finite maximality among graph superproperties
-- statement:
--   For a finite vertex type, if a graph G satisfies a property P, then G has a supergraph M satisfying P that is inclusion maximal among P-supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_cd8388a1_00a6_4989_92c9_fa93d023609b_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧
      ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by sorry
