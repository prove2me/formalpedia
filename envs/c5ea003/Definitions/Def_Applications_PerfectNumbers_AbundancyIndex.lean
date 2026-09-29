-- Prove2me | Definitions.Def_Applications_PerfectNumbers_AbundancyIndex
-- name    : Applications_PerfectNumbers_AbundancyIndex
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:21.941549+00:00
-- url     : https://prove2.me/theorems/bdd9cc13-9e69-4f8f-a160-80fd8c8a305b
-- title:
--   Aether Catalog definitions — Applications_PerfectNumbers_AbundancyIndex
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PerfectNumbers.AbundancyIndex`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PerfectNumbers/AbundancyIndex.lean by skeleton subtraction
import Mathlib

/-!
# The Abundancy Index σ(n)/n

This file develops the **abundancy index** framework for the structural study of
perfect numbers.  For a positive integer `n` the abundancy index is the rational
number `σ(n) / n`, where `σ` is the sum-of-divisors arithmetic function.  A number
is *perfect* exactly when its abundancy index equals `2`, *deficient* when it is
`< 2`, and *abundant* when it is `> 2`.

Main results:

* `PerfectNumbers.abundancy_eq_two_iff_perfect` — `n` is perfect ↔ abundancy `n = 2`.
* `PerfectNumbers.abundancy_mul_coprime` — abundancy is multiplicative on coprime
  arguments (it is a quotient of multiplicative functions).
* `PerfectNumbers.abundancy_prime` — `σ(p)/p = (p+1)/p` for a prime `p`.
* `PerfectNumbers.prime_deficient` — every prime is deficient.
* `PerfectNumbers.primePow_deficient` — every prime power `p^k` (`k ≥ 1`) is deficient.
  This is the key structural lever: a perfect number cannot be a prime power.
* `PerfectNumbers.perfect_not_isPrimePow` — no perfect number is a prime power.
* `PerfectNumbers.perfect_sum_reciprocal_divisors` — for a perfect number,
  `∑_{d ∣ n} 1/d = 2`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The single rational invariant `σ(n)/n` controls the
entire perfect/deficient/abundant trichotomy, and its multiplicativity on coprime
factors plus the strict deficiency of prime powers should already force a perfect
number to have at least two distinct prime factors — a baby version of Nielsen's
"≥ 101 prime factors" bound for odd perfects.

Experiment (Experimenter): Verified `σ(p^k)/p^k < 2` algebraically: clearing the
positive denominator `p - 1` reduces the strict inequality to `0 < p^k (p-2) + 1`,
which `nlinarith`/`positivity` discharge for every prime `p ≥ 2` (note `p = 2`
gives the term `1`).  The multiplicativity uses `isMultiplicative_sigma`.

Analysis (Analyst): The framework cleanly separates the two halves of the
Euclid–Euler picture: the *value* `= 2` (perfection) is a `σ`-identity, while the
*comparison* with `2` is a geometric-series estimate.  Prime powers are uniformly
deficient, so perfection genuinely requires interaction between several primes.

Critique (Critic): All statements quantify over `0 < n`; the `n = 0` edge case is
excluded because `σ(0)/0` is the meaningless `0/0`.  The reciprocal-sum identity
is proved via the involution `d ↦ n/d` on divisors, not by `decide`.

Synthesis (PI): A reusable abundancy API on which the even-perfect structure
theorems (companion file `EvenPerfectStructure.lean`) rest.
-/

open ArithmeticFunction
open scoped sigma

namespace PerfectNumbers

/-- The **abundancy index** of `n`: the rational number `σ(n)/n`. -/
def abundancy (n : ℕ) : ℚ := (σ 1 n : ℚ) / (n : ℚ)

/-- `n` is **deficient** when its abundancy index is `< 2`. -/
def Deficient (n : ℕ) : Prop := abundancy n < 2

/-- `n` is **abundant** when its abundancy index is `> 2`. -/
def Abundant (n : ℕ) : Prop := 2 < abundancy n

/-
`σ(n)` written through the abundancy index: `σ(n) = abundancy n * n`.
-/

/-
A number is perfect iff its abundancy index is exactly `2`.
-/

/-
The abundancy index is multiplicative on coprime arguments.
-/

/-
The abundancy index of a prime `p` is `(p+1)/p`.
-/

/-
Every prime is deficient.
-/

/-
Every prime power `p^k` with `k ≥ 1` is deficient: `σ(p^k)/p^k < 2`.
This is the geometric-series estimate `∑_{i=0}^{k} p^{-i} < p/(p-1) ≤ 2`.
-/

/-
No perfect number is a prime power.  Hence every perfect number has at least
two distinct prime factors.
-/

/-
A perfect number has at least two distinct prime factors.
-/

/-
For a perfect number, the sum of reciprocals of its divisors is exactly `2`.
-/

/-
`12` is abundant: a concrete witness that abundant numbers exist.
-/

end PerfectNumbers


