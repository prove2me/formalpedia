-- Prove2me | solution 1 for BookSixth.prod_Icc_pow_factorial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:35:12.195792+00:00
-- url     : https://prove2.me/submissions/1a421e8a-0c51-45f9-8059-e714111e7cbc

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : ℕ) :
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
