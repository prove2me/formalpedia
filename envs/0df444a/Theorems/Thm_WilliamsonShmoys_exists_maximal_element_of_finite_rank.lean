-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_element_of_finite_rank
-- name    : WilliamsonShmoys.exists_maximal_element_of_finite_rank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:13:39.918757+00:00
-- url     : https://prove2.me/theorems/dba088f8-996c-4d6d-97e5-78d5c9c2732a
-- title:
--   A finite ranked candidate set has a maximal element
-- statement:
--   For a finite type, if there is at least one candidate and every distinct comparable pair of candidates has strictly increasing rank, then some candidate has no distinct candidate above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_element_of_finite_rank {α : Type} [Fintype α] (P : α → Prop) (R : α → α → Prop) (rank : α → Nat) (hP : ∃ x, P x) (hRank : ∀ x y, P x → P y → R x y → x ≠ y → rank x < rank y) : ∃ x, P x ∧ ∀ y, P y → R x y → y = x := by sorry
