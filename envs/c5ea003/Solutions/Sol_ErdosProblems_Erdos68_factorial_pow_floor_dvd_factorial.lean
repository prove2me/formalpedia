-- Prove2me | solution 1 for ErdosProblems.Erdos68.factorial_pow_floor_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:13:09.599993+00:00
-- url     : https://prove2.me/submissions/9913749b-831e-4d07-a35f-2158afede373

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Theorems.Thm_ErdosProblems_Erdos68_factorial_pow_dvd_factorial_of_dvd
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
    d.factorial ^ (i / d) ∣ i.factorial := by
  have hdiv : d ∣ d * (i / d) := dvd_mul_right d (i / d)
  have hpow :=
    factorial_pow_dvd_factorial_of_dvd hdiv
  have hquot : (d * (i / d)) / d = i / d := by
    simpa [Nat.mul_comm] using Nat.mul_div_left (i / d) hd
  rw [hquot] at hpow
  exact hpow.trans
    (Nat.factorial_dvd_factorial (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self i d))
