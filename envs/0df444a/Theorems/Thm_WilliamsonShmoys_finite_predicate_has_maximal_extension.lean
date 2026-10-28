-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_extension
-- name    : WilliamsonShmoys.finite_predicate_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:50:50.819801+00:00
-- url     : https://prove2.me/theorems/7984e2af-31d0-46fa-bde2-6731a7647ce6
-- title:
--   Maximal extension for a predicate on finite simple graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal among predicate-satisfying graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_has_maximal_extension
    {V : Type} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ R N ∧
      ∀ P : SimpleGraph V, N ≤ P → R P → P = N := by
  sorry
