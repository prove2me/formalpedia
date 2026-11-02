-- Prove2me | Theorems.Thm_exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- name    : exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:09.994434+00:00
-- url     : https://prove2.me/theorems/19ae8fdb-9e6b-47f1-b9c6-735569829672
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partial order, any predicate holding at a has a maximal satisfying element above it. This isolates the finite extremal argument independently of graphs or drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_above_in_finite_type__p2m_0d7f4e6a_f018_419b_9ff8_3c6696d14d6d_a1 {α : Type} [Finite α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ b, P b ∧ a ≤ b ∧ ∀ c, b ≤ c → P c → c = b := by sorry
