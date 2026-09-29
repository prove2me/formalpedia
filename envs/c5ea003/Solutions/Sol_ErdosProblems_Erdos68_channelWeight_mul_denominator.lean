-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelWeight_mul_denominator
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:37.782956+00:00
-- url     : https://prove2.me/submissions/8bbf44e2-fa77-47e6-afe8-d3a545f7c442

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Theorems.Thm_ErdosProblems_Erdos68_factorial_pow_floor_dvd_factorial
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Erdős #68: factorial-channel certificates

For each divisor channel `d`, the weight

`i! / (d!)^(⌊i/d⌋)`

is integral, and consecutive weights obey the factorial recurrence except at
indices divisible by `d`.  The coefficient vector `λ = 2e₃ - e₄` then gives
an explicit finite certificate: its channel values and factorial moment can be
computed exactly, and the stated elementary enclosure for the remaining tail
places its residual strictly between `-1` and `0`.

This is a single finite certificate.  It does not supply a cofinal family of
nonzero residuals or prove irrationality of the Erdős #68 series.
-/

open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    (i d : ℕ) (hd : 0 < d) :
    d.factorial ^ (i / d) * channelWeight i d =
      i.factorial := by
  exact Nat.mul_div_cancel'
    (factorial_pow_floor_dvd_factorial i d hd)
