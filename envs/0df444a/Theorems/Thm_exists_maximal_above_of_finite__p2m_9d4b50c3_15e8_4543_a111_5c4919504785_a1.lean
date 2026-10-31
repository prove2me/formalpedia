-- Prove2me | Theorems.Thm_exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- name    : exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:50.985519+00:00
-- url     : https://prove2.me/theorems/d01db038-54b1-43a2-b54d-f083d4279688
-- title:
--   Maximal satisfying element above a point in a finite partial order
-- statement:
--   In a finite partial order, if an element satisfies a predicate, there is a maximal satisfying element above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_above_of_finite__p2m_9d4b50c3_15e8_4543_a111_5c4919504785_a1 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by sorry
