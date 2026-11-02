-- Prove2me | Theorems.Thm_exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
-- name    : exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:19.882628+00:00
-- url     : https://prove2.me/theorems/d4eb7d83-dee2-4823-a7d5-58444a1cfd2a
-- title:
--   Finite maximal feasible extension
-- statement:
--   In a finite partial order, every feasible element has a feasible extension that is maximal among feasible elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_feasible_extension_finite__p2m_53772a33_25fb_4be5_bc25_56c0a0bf34f9_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by sorry
