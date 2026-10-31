-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:28:31.695351+00:00
-- url     : https://prove2.me/theorems/91679956-35e3-4946-9959-2a580d3a4fba
-- title:
--   Finite maximal supergraph for an arbitrary predicate
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, if H satisfies the predicate, then H has a supergraph K satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_3043441f_698f_49eb_9867_9197561360be_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
