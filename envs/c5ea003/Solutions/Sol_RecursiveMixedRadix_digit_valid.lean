-- Prove2me | solution 1 for RecursiveMixedRadix.digit_valid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:40:43.297316+00:00
-- url     : https://prove2.me/submissions/598d1b06-7d88-4d5e-b9dc-bcd8d41132c1

-- Sol generated from NumberTheory/RecursiveMixedRadix.lean
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix

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
theorem solution{r : ℕ → ℕ} (hr : ∀ i, 0 < r i) (n k : ℕ) :
    Valid r (digit r n) k := by
  intro i _
  exact Nat.mod_lt _ (hr i)
