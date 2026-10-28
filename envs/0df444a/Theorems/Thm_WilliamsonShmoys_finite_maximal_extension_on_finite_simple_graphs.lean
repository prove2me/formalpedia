-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_on_finite_simple_graphs
-- name    : WilliamsonShmoys.finite_maximal_extension_on_finite_simple_graphs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:39:25.251738+00:00
-- url     : https://prove2.me/theorems/ca9f3aa7-5054-47f6-a86d-07e8da5ae0de
-- title:
--   Finite maximal extension for a predicate on simple graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension_on_finite_simple_graphs
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
