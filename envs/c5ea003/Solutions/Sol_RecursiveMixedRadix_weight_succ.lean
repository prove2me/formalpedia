-- Prove2me | solution 1 for RecursiveMixedRadix.weight_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:37:21.798962+00:00
-- url     : https://prove2.me/submissions/052fec9d-be41-452a-b5ff-c3f44f0d440e

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
@[simp] theorem solution(r : ℕ → ℕ) (k : ℕ) :
    weight r (k + 1) = r k * weight r k := by rfl
