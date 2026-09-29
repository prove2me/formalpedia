-- Prove2me | Definitions.Def_Applications_Pythagorean_StrongDivisibilitySequences
-- name    : Applications_Pythagorean_StrongDivisibilitySequences
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:35.001147+00:00
-- url     : https://prove2.me/theorems/0ae9b9bb-3256-46d3-b65f-a60b6d080276
-- title:
--   Aether Catalog definitions — Applications_Pythagorean_StrongDivisibilitySequences
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Pythagorean.StrongDivisibilitySequences`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Pythagorean/StrongDivisibilitySequences.lean by skeleton subtraction
import Mathlib

/-! # Strong divisibility sequences: abstract primitive divisors and apparition

Domain: Algebra / Number Theory (Applications).

This file **generalizes** the Fibonacci-specific results of
`Catalog/Applications/FibonacciPrimitiveDivisors.lean` to *arbitrary strong divisibility
sequences*.  A sequence `u : ℕ → ℕ` is a **strong divisibility sequence** (`IsStrongDivSeq`)
when `u (gcd m n) = gcd (u m) (u n)` for all `m, n`.  The Fibonacci file used **only** the
two facts `Nat.fib_gcd` and `Nat.fib_dvd`; both are instances of this single hypothesis, so
the entire primitivity/apparition theory lifts verbatim.  This realizes **Direction 3** of the
previous cycle's `FUTURE_DIRECTIONS.md` ("Abstract strong divisibility sequences") and, via the
counting corollaries, **Direction 5** ("Counting simultaneous apparitions / density").

Two concrete instances are recorded:

* `fib_isStrongDivSeq`     — the Fibonacci sequence `Nat.fib` (from `Nat.fib_gcd`); this
  recovers every result of `FibonacciPrimitiveDivisors`.
* `mersenne_isStrongDivSeq`— the sequence `n ↦ a ^ n - 1` (from
  `Nat.pow_sub_one_gcd_pow_sub_one`), i.e. the Mersenne / `aⁿ−1` family.

Main results (all stated for an arbitrary `u`):

* `IsStrongDivSeq.dvd_of_dvd`         — `m ∣ n → u m ∣ u n` (the weak divisibility law).
* `IsStrongDivSeq.dvd_gcd_index_iff`  — the sharp meet law `d ∣ u (gcd m n) ↔ d ∣ u m ∧ d ∣ u n`.
* `isPrimitive_unique`                — a value is primitive for at most one positive index.
* `dvd_iff_index_dvd_of_primitive`    — a primitive divisor pins divisibility to multiples of its index.
* `simultaneous_apparition`           — the join law `(p ∣ u n ∧ q ∣ u n) ↔ lcm a b ∣ n`.
* `simultaneous_apparition_finset`    — the finite-family generalization.
* `apparition_count`                  — `#{e < N : p ∣ u (e+1)} = N / n` (density `1/n`).
* `simultaneous_apparition_count`     — `#{e < N : p ∣ u(e+1) ∧ q ∣ u(e+1)} = N / lcm a b`.
-/

namespace StrongDivSeq

/-- A **strong divisibility sequence**: `u (gcd m n) = gcd (u m) (u n)` for all `m, n`.
Both `Nat.fib` and `n ↦ aⁿ − 1` satisfy this. -/
def IsStrongDivSeq (u : ℕ → ℕ) : Prop :=
  ∀ m n, u (Nat.gcd m n) = Nat.gcd (u m) (u n)

/-- `p` is a *primitive divisor* of `u n`: it divides `u n` but none of `u 1, …, u (n-1)`. -/
def IsPrimitive (u : ℕ → ℕ) (p n : ℕ) : Prop :=
  p ∣ u n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ u k

/-! ## §1. Elementary consequences of the strong-divisibility law -/

/-
!-- Lab Notebook: IsStrongDivSeq.dvd_of_dvd -- !--
!-- Hypothesis: A strong divisibility sequence is in particular a divisibility sequence:
`m ∣ n → u m ∣ u n` (generalizing `Nat.fib_dvd`). -- !--
!-- Result: Proved. `m ∣ n` gives `gcd m n = m`, so `u m = u (gcd m n) = gcd (u m) (u n)`
divides `u n` by `Nat.gcd_dvd_right`. -- !--
!-- Insight: The *weak* law (Mathlib's `Nat.fib_dvd`) is a free corollary of the *strong* law;
no extra hypothesis is needed. -- !--
!-- Failure analysis: none. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: IsStrongDivSeq.dvd_gcd_index_iff -- !--
!-- Hypothesis: For ANY divisor `d`, `d ∣ u (gcd m n) ↔ d ∣ u m ∧ d ∣ u n`
(generalizing `FibonacciPrimitiveDivisors.fib_dvd_gcd_iff`). -- !--
!-- Result: Proved by rewriting with the strong-divisibility law and `Nat.dvd_gcd_iff`. -- !--
!-- Insight: This is the lattice "meet" law at the level of raw divisors, valid in every
strong divisibility sequence. -- !--
!-- Failure analysis: none. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §2. Rigidity: a value is primitive for at most one index -/

/-
!-- Lab Notebook: isPrimitive_zero_everything -- !--
!-- Hypothesis: Every modulus is vacuously primitive at index `0`. -- !--
!-- Result: Proved: `p ∣ u 0 ... ` need not hold for general `u`! Instead the minimality
clause is vacuous; but `p ∣ u 0` requires `u 0 = 0`. We therefore require `u 0 = 0`. -- !--
!-- Insight: For Fibonacci `u 0 = 0` automatically; in the abstract setting the boundary
fact needs `u 0 = 0` as a hypothesis, pinning down why positivity is required elsewhere. -- !--
!-- Failure analysis: dropping `u 0 = 0` makes index-0 primitivity fail. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: isPrimitive_unique -- !--
!-- Hypothesis: A value cannot be a primitive divisor of two different positive indices. -- !--
!-- Result: Proved by a direct minimality clash; NO strong-divisibility hypothesis needed.
If `m < n`, primitivity at `n` forbids `p ∣ u m`, contradicting primitivity at `m`. -- !--
!-- Insight: Primitivity is so rigid that uniqueness is immediate from the definition. -- !--
!-- Failure analysis: index 0 must be excluded (see isPrimitive_zero_everything). -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §3. A primitive divisor pins down the divisibility set -/

/-
!-- Lab Notebook: dvd_iff_index_dvd_of_primitive -- !--
!-- Hypothesis: If `p` is primitive for `u n` then `p ∣ u m ↔ n ∣ m`
(generalizing `FibonacciPrimitiveDivisors.dvd_fib_iff_index_dvd_of_primitive`). -- !--
!-- Result: Proved. Backward: `n ∣ m → u n ∣ u m` (`dvd_of_dvd`), and `p ∣ u n`.
Forward: from `p ∣ u m, u n` get `p ∣ u (gcd n m)` (meet law); minimality forces
`gcd n m = n`, i.e. `n ∣ m`. -- !--
!-- Insight: Primitivity upgrades the abstract apparition law to a concrete divisibility
test, derived straight from the meet law. -- !--
!-- Failure analysis: needs the strong-divisibility hypothesis (for the meet law) and `0<n`. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §4. Simultaneous apparition: the join law -/

/-
!-- Lab Notebook: simultaneous_apparition -- !--
!-- Hypothesis: For primitive divisors `p` (of `u a`) and `q` (of `u b`), both divide `u n`
exactly at the multiples of `lcm a b`. -- !--
!-- Result: Proved: rewrite each conjunct via `dvd_iff_index_dvd_of_primitive`, then
`Nat.lcm_dvd_iff`. -- !--
!-- Insight: The common-apparition set of two primitive divisors is itself an apparition
class governed by the lcm of the two indices. -- !--
!-- Failure analysis: both indices must be positive. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: simultaneous_apparition_finset -- !--
!-- Hypothesis: For a finite family with each `f i` primitive for `u (g i)`, all `f i`
divide `u n` iff the lcm of the indices `g i` divides `n`. -- !--
!-- Result: Proved by `Finset.induction` combining `dvd_iff_index_dvd_of_primitive`
with `Nat.lcm_dvd_iff` and `Finset.lcm_insert`. -- !--
!-- Insight: Expresses the full common-apparition set of a family as a single apparition class. -- !--
!-- Failure analysis: `Finset.lcm ∅ = 1 ∣ n` handles the base case. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §5. Counting / density of apparition indices (Direction 5) -/

/-
!-- Lab Notebook: apparition_count -- !--
!-- Hypothesis: Among the first `N` positive indices, exactly `N / n` of them are apparition
indices of a primitive divisor `p` of `u n`. -- !--
!-- Result: Proved: `dvd_iff_index_dvd_of_primitive` turns the filter predicate
`p ∣ u (e+1)` into `n ∣ (e+1)`, and `Nat.card_multiples` counts those as `N / n`. -- !--
!-- Insight: The natural-density of apparition indices of a primitive divisor of index `n`
is exactly `1/n`; this is the quantitative face of the pinning law. -- !--
!-- Failure analysis: uses the `+1` shift so that index `0` (where everything divides) is
excluded, matching `Nat.card_multiples`. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: simultaneous_apparition_count -- !--
!-- Hypothesis: Among the first `N` positive indices, exactly `N / lcm a b` are joint
apparition indices of primitive divisors `p` (of `u a`) and `q` (of `u b`). -- !--
!-- Result: Proved: `simultaneous_apparition` turns the joint predicate into
`lcm a b ∣ (e+1)`, then `Nat.card_multiples`. -- !--
!-- Insight: Joint apparition has density `1 / lcm a b`, connecting the apparition lattice
to analytic density. -- !--
!-- Failure analysis: same `+1` shift convention as `apparition_count`. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §6. Concrete instances: Fibonacci and Mersenne (`aⁿ − 1`) -/

/-
!-- Lab Notebook: fib_isStrongDivSeq -- !--
!-- Hypothesis: `Nat.fib` is a strong divisibility sequence. -- !--
!-- Result: Immediate from `Nat.fib_gcd`. -- !--
!-- Insight: Every theorem above instantiates to the Fibonacci results of the previous cycle. -- !--
!-- End Lab Notebook -- !--
-/

/-
!-- Lab Notebook: mersenne_isStrongDivSeq -- !--
!-- Hypothesis: For any base `a`, the sequence `n ↦ aⁿ − 1` is a strong divisibility sequence. -- !--
!-- Result: Immediate from `Nat.pow_sub_one_gcd_pow_sub_one`. -- !--
!-- Insight: The same primitivity/apparition theory governs Mersenne-type sequences,
a genuine cross-domain consolidation. -- !--
!-- End Lab Notebook -- !--
-/

end StrongDivSeq


