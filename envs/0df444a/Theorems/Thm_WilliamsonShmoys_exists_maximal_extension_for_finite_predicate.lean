-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_finite_predicate
-- name    : WilliamsonShmoys.exists_maximal_extension_for_finite_predicate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:22:16.136131+00:00
-- url     : https://prove2.me/theorems/e62ae62c-8b82-4be2-9221-9653d5c22462
-- title:
--   A predicate on finite graphs has maximal extensions
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

open SimpleGraph

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_for_finite_predicate {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) : ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧ ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by sorry
