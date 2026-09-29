-- Prove2me | solution 1 for Dynamics.periodic_of_shift_smul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:29.950629+00:00
-- url     : https://prove2.me/submissions/ce9b7d30-629c-4c0c-8e3a-28603f227279

import Mathlib

theorem solution {X G : Type*} [Group G] [Finite G] [MulAction G X]
    (c : ℝ → X) (w : G) (lam : ℝ) (hshift : ∀ s : ℝ, c (s + lam) = w • c s) :
    Function.Periodic c ((orderOf w : ℕ) * lam) := by
  have iter : ∀ n : ℕ, ∀ s : ℝ, c (s + n * lam) = (w ^ n) • c s := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      have hrw : s + ((n : ℝ) + 1) * lam = (s + n * lam) + lam := by ring
      push_cast
      rw [hrw, hshift, ih, smul_smul, ← pow_succ']
  intro s
  rw [iter (orderOf w) s, pow_orderOf_eq_one, one_smul]
