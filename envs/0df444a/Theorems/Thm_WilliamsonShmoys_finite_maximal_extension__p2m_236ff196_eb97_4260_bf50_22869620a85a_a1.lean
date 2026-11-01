-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:59.04363+00:00
-- url     : https://prove2.me/theorems/f3a3fc9f-d603-44dd-babb-f1fcf8125464
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For a finite ordered vertex type, every graph satisfying a predicate has a predicate-satisfying supergraph that is maximal among predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_236ff196_eb97_4260_bf50_22869620a85a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ L : SimpleGraph V,
      P L ∧
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V,
        P M →
        (∀ u v, L.Adj u v → M.Adj u v) →
        ∀ u v, M.Adj u v → L.Adj u v) := by sorry
