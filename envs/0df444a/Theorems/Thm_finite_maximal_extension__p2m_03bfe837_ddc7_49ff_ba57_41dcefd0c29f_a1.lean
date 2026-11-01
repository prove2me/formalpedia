-- Prove2me | Theorems.Thm_finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- name    : finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:19.098322+00:00
-- url     : https://prove2.me/theorems/9e120d86-45f5-4055-bb84-d36503d6592f
-- title:
--   Maximal feasible element in a finite partial order
-- statement:
--   In a finite partially ordered type, any element satisfying a downward-closed predicate lies below a maximal element satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximal_extension__p2m_03bfe837_ddc7_49ff_ba57_41dcefd0c29f_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {a b : α}, a ≤ b → P b → P a)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by sorry
