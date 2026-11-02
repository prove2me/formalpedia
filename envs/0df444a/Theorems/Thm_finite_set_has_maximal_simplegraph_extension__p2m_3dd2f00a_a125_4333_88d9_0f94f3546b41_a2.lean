-- Prove2me | Theorems.Thm_finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2
-- name    : finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:57.794986+00:00
-- url     : https://prove2.me/theorems/6639b8bd-5959-456e-874f-efbd7d5aa5ab
-- title:
--   A finite nonempty set of finite graphs has an inclusion-maximal member
-- statement:
--   Every finite nonempty set of simple graphs on a finite linearly ordered vertex type contains a graph maximal under inclusion within that set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

set_option autoImplicit false

theorem finite_set_has_maximal_simplegraph_extension__p2m_3dd2f00a_a125_4333_88d9_0f94f3546b41_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set (SimpleGraph V)) (hS : S.Finite) (hne : S.Nonempty) :
    ∃ K ∈ S, ∀ L ∈ S, K ≤ L → L ≤ K := by sorry
