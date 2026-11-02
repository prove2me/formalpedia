-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:54:51.876916+00:00
-- url     : https://prove2.me/theorems/4b217596-a7d3-4fcf-8569-68084f2cf0c3
-- title:
--   Finite maximal extension for a predicate on simple graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, if a graph satisfies the predicate, it has a predicate-satisfying supergraph that is inclusion-maximal among predicate-satisfying graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_028c3839_39ea_4f46_a39d_0709e61e420f_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by sorry
