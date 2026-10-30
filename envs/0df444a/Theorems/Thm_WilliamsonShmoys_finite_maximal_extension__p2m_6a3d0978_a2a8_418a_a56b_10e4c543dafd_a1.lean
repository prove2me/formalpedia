-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:47.070347+00:00
-- url     : https://prove2.me/theorems/7a02e70f-fc61-442e-a193-09698b981594
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For a finite linearly ordered vertex type, any graph satisfying a predicate has a supergraph satisfying that predicate that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_extension__p2m_6a3d0978_a2a8_418a_a56b_10e4c543dafd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by sorry
