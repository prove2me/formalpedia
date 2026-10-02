-- Prove2me | solution 1 for BookSixth.latin_lower_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:24:45.505452+00:00
-- url     : https://prove2.me/submissions/cc868190-f6f5-4222-a20e-31bc692cdea3

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem rowprod_identity (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (k : ℝ) ^ n = (n.factorial : ℝ) ^ n := by
  have hfact : ∀ m : ℕ, ∏ k ∈ Finset.Icc 1 m, (k : ℝ) = (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero =>
      rw [show Finset.Icc 1 (0 : ℕ) = ∅ by decide, Finset.prod_empty]
      simp
    | succ m ih =>
      rw [Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega) (fun k => (k : ℝ)), ih,
        Nat.factorial_succ, Nat.cast_mul]
      ring
  rw [Finset.prod_pow, hfact n]

theorem solution (n : ℕ) (e : ℕ → ℝ)
    (hstep : ∀ k ∈ Finset.Icc 1 n,
      (n.factorial : ℝ) * ((k : ℝ) ^ n / (n : ℝ) ^ n) ≤ e k) :
    (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n * n)
      ≤ ∏ k ∈ Finset.Icc 1 n, e k := by
  have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
  have hrow := rowprod_identity n
  have hnn2 : n + n = 2 * n := by omega
  have e1 : ∏ _k ∈ Finset.Icc 1 n, (n.factorial : ℝ)
        = (n.factorial : ℝ) ^ n := by
    simp [Finset.prod_const, hcard]
  have e2 : ∏ _k ∈ Finset.Icc 1 n, (n : ℝ) ^ n
        = ((n : ℝ) ^ n) ^ n := by
    simp [Finset.prod_const, hcard]
  have h1 : ∏ k ∈ Finset.Icc 1 n,
        ((n.factorial : ℝ) * ((k : ℝ) ^ n / (n : ℝ) ^ n))
        = (n.factorial : ℝ) ^ (2 * n) / (n : ℝ) ^ (n * n) := by
    rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, hrow, e1, e2,
      ← pow_mul, ← mul_div_assoc, ← pow_add, hnn2]
  rw [← h1]
  apply Finset.prod_le_prod
  · intro k hk
    positivity
  · intro k hk
    exact hstep k hk
