-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelEvent_eq_zero_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:38.302771+00:00
-- url     : https://prove2.me/submissions/5bf05d6d-a960-4efd-8699-025b0fc0657c

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
    {d n : ℕ} (hd : 2 ≤ d) (hnd : ¬ d ∣ n) :
    channelEvent d n = 0 := by
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    exact hnd (hn0 ▸ dvd_zero d)
  have hdpos : 0 < d := by omega
  have hmodNe : n % d ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnd
  have hmodPos : 0 < n % d := Nat.pos_of_ne_zero hmodNe
  have hmodLt : n % d < d := Nat.mod_lt n hdpos
  have hnrepr : n / d * d + n % d = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n d
  have hfloor : (n - 1) / d = n / d := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using
        (show n / d * d ≤ n - 1 by omega)
    · rw [Nat.add_mul, one_mul]
      omega
  have hdenDvd :
      d.factorial ^ (n / d) ∣ (n - 1).factorial := by
    rw [← hfloor]
    exact factorial_pow_floor_dvd_factorial (n - 1) d hdpos
  have hfac : n.factorial = n * (n - 1).factorial := by
    have hn : n - 1 + 1 = n := by omega
    simpa only [hn] using Nat.factorial_succ (n - 1)
  have hweight :
      channelWeight n d = n * channelWeight (n - 1) d := by
    rw [channelWeight, channelWeight, hfloor, hfac]
    symm
    exact (Nat.mul_div_assoc n hdenDvd).symm
  simp [channelEvent, hweight]
