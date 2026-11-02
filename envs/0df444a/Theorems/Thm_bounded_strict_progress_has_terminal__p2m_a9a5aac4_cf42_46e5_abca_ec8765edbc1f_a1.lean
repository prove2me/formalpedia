-- Prove2me | Theorems.Thm_bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
-- name    : bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:55.327022+00:00
-- url     : https://prove2.me/theorems/235fc8e8-00e9-4a23-a9e1-1be08db6e803
-- title:
--   A bounded strict-progress process has a terminal state
-- statement:
--   If there is an initial state satisfying P, all P-states have a natural-number measure bounded by N, and every P-state failing Q has a P-state of strictly larger measure, then some P-state satisfies Q.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem bounded_strict_progress_has_terminal__p2m_a9a5aac4_cf42_46e5_abca_ec8765edbc1f_a1
    {α : Type} (P Q : α → Prop) (μ : α → Nat) (N : Nat)
    (hbase : ∃ a : α, P a)
    (hbound : ∀ a : α, P a → μ a ≤ N)
    (hprogress : ∀ a : α, P a → ¬ Q a → ∃ b : α, P b ∧ μ a < μ b) :
    ∃ a : α, P a ∧ Q a := by sorry
