-- Prove2me | solution 1 for ErdosProblems.Erdos68.factorial_pow_dvd_factorial_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:11:13.07718+00:00
-- url     : https://prove2.me/submissions/42571f7d-1135-4f4e-8019-a6ba01390357

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ErdosProblems.Erdos68
end ErdosProblems.Erdos68

open scoped BigOperators

/-!
# Erdős #68: factorial carries and prime windows

For

`S = ∑ n ≥ 2, 1 / (n! - 1)`,

expanding each summand geometrically and regrouping by `m = n * j`
produces the integral coefficient

`C_m = ∑_{d ∣ m, 2 ≤ d} m! / (d!)^(m/d)`.

The multinomial divisibility proved below shows directly that every summand is
an integer.  The same arithmetic leads to a finite interval question at prime
dilations: an integral carry must lie in a prescribed residue class inside a
rational window.  A missed window therefore excludes that carry, and a window
of length less than one contains at most one possible integer.

These statements do not prove that the windows arising from the series are
missed for infinitely many primes, and they do not prove irrationality.
-/

open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution
    {d m : ℕ} (hd : d ∣ m) :
    d.factorial ^ (m / d) ∣ m.factorial := by
  have h := Nat.prod_factorial_dvd_factorial_sum
    (Finset.range (m / d)) (fun _ : ℕ => d)
  simpa [Finset.prod_const, Finset.sum_const, Nat.div_mul_cancel hd] using h
