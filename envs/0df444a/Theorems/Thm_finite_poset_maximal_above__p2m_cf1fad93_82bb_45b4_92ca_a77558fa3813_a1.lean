-- Prove2me | Theorems.Thm_finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1
-- name    : finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:01:32.626846+00:00
-- url     : https://prove2.me/theorems/8b027b81-5dde-4872-a6e0-2bf6d7c5c40e
-- title:
--   A finite partially ordered type has a maximal element above any satisfying point
-- statement:
--   In a finite partially ordered type, any point satisfying a predicate lies below a predicate-satisfying maximal point.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_poset_maximal_above__p2m_cf1fad93_82bb_45b4_92ca_a77558fa3813_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) {a : α} (ha : P a) :
    ∃ m, a ≤ m ∧ P m ∧ ∀ b, m ≤ b → P b → b ≤ m := by sorry
