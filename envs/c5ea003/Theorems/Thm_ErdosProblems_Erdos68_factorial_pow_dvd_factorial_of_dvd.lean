-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_factorial_pow_dvd_factorial_of_dvd
-- name    : ErdosProblems.Erdos68.factorial_pow_dvd_factorial_of_dvd
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:05:30.557162+00:00
-- url     : https://prove2.me/theorems/51f5bb0f-253c-44cf-a744-748eaad04b0a
-- title:
--   Factorial pow divisibility factorial of divisibility
-- statement:
--   If d divides m, then (d factorial) to the power m/d divides m factorial.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialCarry.lean#L36-L41
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

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

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.factorial_pow_dvd_factorial_of_dvd
    {d m : ℕ} (hd : d ∣ m) :
    d.factorial ^ (m / d) ∣ m.factorial := by sorry
