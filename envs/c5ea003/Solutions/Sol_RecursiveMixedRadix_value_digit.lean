-- Prove2me | solution 1 for RecursiveMixedRadix.value_digit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:43:05.840947+00:00
-- url     : https://prove2.me/submissions/f19cb7d9-0e14-4178-8e61-b32573960a22

-- Sol generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix
import Theorems.Thm_RecursiveMixedRadix_digit_decomposition

/-!
# Recursive mixed-radix representations

This file isolates the general mixed-radix mechanism behind factoradics and
recursive-base systems.  A radix sequence `r` determines place values
`weight r 0 = 1` and `weight r (k+1) = r k * weight r k`.

The main results prove, constructively and without cardinality arguments, that
valid length-`k` digit strings represent exactly the naturals below
`weight r k`, and do so uniquely.
-/

open RecursiveMixedRadix

open Finset


















open RecursiveMixedRadix in
theorem solution{r : ℕ → ℕ} {n k : ℕ}
    (hn : n < weight r k) : value r (digit r n) k = n := by
  have hdiv : n / weight r k = 0 := Nat.div_eq_of_lt hn
  have h := digit_decomposition (r := r) n k
  simp [hdiv] at h
  exact h.symm
