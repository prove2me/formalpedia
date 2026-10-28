-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_rank_extension_reaches_terminal
-- name    : WilliamsonShmoys.finite_rank_extension_reaches_terminal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:26:34.247001+00:00
-- url     : https://prove2.me/theorems/094cff20-fdcc-430f-be65-681127ccd3bc
-- title:
--   Bounded rank extensions reach a terminal element
-- statement:
--   If an element satisfying P has rank at most B, and every P-element that is not terminal has a P-extension of strictly larger rank still at most B, then some P-element is terminal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_rank_extension_reaches_terminal
    {α : Type} (rank : α → Nat) (P T : α → Prop) (a : α) (B : Nat)
    (ha : P a) (haB : rank a ≤ B)
    (hstep : ∀ x : α, P x → ¬ T x →
      ∃ y : α, P y ∧ rank x < rank y ∧ rank y ≤ B) :
    ∃ x : α, P x ∧ T x := by sorry
