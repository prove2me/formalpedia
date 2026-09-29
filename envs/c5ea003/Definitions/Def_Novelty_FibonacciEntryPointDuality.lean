-- Prove2me | Definitions.Def_Novelty_FibonacciEntryPointDuality
-- name    : Novelty_FibonacciEntryPointDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:11.790759+00:00
-- url     : https://prove2.me/theorems/e48e362d-de39-489d-a93e-736cdc2bed63
-- title:
--   Aether Catalog definitions — Novelty_FibonacciEntryPointDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FibonacciEntryPointDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FibonacciEntryPointDuality.lean by skeleton subtraction
import Mathlib

/-!
# Entry-Point Duality for the Fibonacci sequence

For a modulus `p`, the **entry point** (rank of apparition) `z(p) = fibEntry p` is the
least positive index `k` with `p ∣ F k` (and `0` if no such index exists).  This file
isolates the single biconditional from which the scattered, one-directional
entry-point lemmas of the catalog all follow:

* `fib_dvd_iff_fibEntry_dvd` — the master *duality* `p ∣ F n ↔ z(p) ∣ n`.  It turns a
  divisibility question about Fibonacci numbers into a divisibility question about a
  single arithmetic function `z`.
* `isFibPrimitiveDivisor_iff_entry` — a prime `p` is a *primitive* divisor of `F n`
  iff `z(p) = n`; primitivity collapses to one equation.
* `fib_dvd_iff` — the strong-divisibility law `F m ∣ F n ↔ m ∣ n` for `m ≥ 3`,
  recovered as the special case `p = F m` of the duality.
* `fib_primitive_divisor_verified` — a `native_decide` certificate of Carmichael's
  primitive-divisor theorem for `1 ≤ n ≤ 40`, `n ∉ {1,2,6,12}`.

The whole development is self-contained over Mathlib: the only Fibonacci-specific
inputs are `Nat.fib_gcd` and `Nat.fib_dvd`.

## Catalog synthesis

This unifies and generalizes the one-directional entry-point lemmas previously
scattered across the catalog: `CarmichaelComposite.fibEntryPt_dvd_of_fib_dvd`
(forward direction only, stated for primes), the LTE file's `fibEntryPoint`, and the
primitive-divisor predicates of `Applications.FibonacciPrimitiveDivisors`.  The new
content is that all of these are corollaries of one biconditional, which moreover
needs no primality hypothesis.

-- !-- Lab Notebook -- !--
-- !-- Hypothesis: the divisibility relation `p ∣ F n` is governed entirely by the
--     entry-point map `z`, via the principal-ideal identity `p ∣ F n ↔ z(p) ∣ n`,
--     with no primality hypothesis required. -- !--
-- !-- Result: proved the biconditional for arbitrary `p`, derived the primitive-divisor
--     characterization `z(p)=n`, the strong-divisibility law `F m ∣ F n ↔ m ∣ n`
--     (`m ≥ 3`), and a finite Carmichael certificate. -- !--
-- !-- Insight: `Nat.fib_gcd` collapses "two simultaneous apparitions" into one
--     apparition at the gcd, so minimality of `z(p)` forces `z(p) ∣ n`; the converse
--     is pure `Nat.fib_dvd`.  Everything else is divisibility algebra in ℕ. -- !--
-- !-- Failure analysis: the only care needed is the `n = 0` / "no entry point" boundary,
--     handled uniformly because `0 ∣ n ↔ n = 0` and `F 0 = 0`. -- !--
-- !-- End Lab Notebook -- !--
-/

namespace FibEntryDuality

open Classical in
/-- The **Fibonacci entry point** (rank of apparition) of `p`: the least positive `k`
with `p ∣ F k`, or `0` if no such `k` exists. -/
noncomputable def fibEntry (p : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ p ∣ Nat.fib k then Nat.find h else 0

/-
!-- If `p ∣ F a` and `p ∣ F b` then `p ∣ F (gcd a b)`, since `F (gcd a b) = gcd (F a) (F b)`. -- !--
-/

/-
!-- The master duality: `p ∣ F n` iff the entry point of `p` divides `n`.  Forward by
minimality of the entry point applied to `F (gcd n (z p)) = gcd (F n) (F (z p))`;
backward by `Nat.fib_dvd`.  Boundary `n = 0` is handled by `0 ∣ n ↔ n = 0`. -- !--
-/

/-- `p` is a **primitive prime divisor** of `F n`: a prime dividing `F n` but none of
the earlier (positive index) Fibonacci numbers. -/
def IsFibPrimitiveDivisor (p n : ℕ) : Prop :=
  Nat.Prime p ∧ p ∣ Nat.fib n ∧ ∀ k, k < n → 0 < k → ¬ p ∣ Nat.fib k

/-
!-- Primitivity collapses to the single equation `z(p) = n`: a prime dividing `F n`
(with `n > 0`) is primitive iff its entry point is exactly `n`, both directions
via `fib_dvd_iff_fibEntry_dvd`. -- !--
-/

/-
!-- The entry point of `F m` is `m` for `m ≥ 3`: `z(F m) ∣ m` by the duality, and
`F (z) = F m` by mutual divisibility forces `z = m` since `fib` is injective on
indices `≥ 3`. -- !--
-/

/-
!-- Strong divisibility: `F m ∣ F n ↔ m ∣ n` for `m ≥ 3`, the special case `p = F m`
of the duality together with `fibEntry_fib`. -- !--
-/

/-- An explicit table of least primitive prime divisors of `F n` for `n ≤ 40`
(`0` for the exceptional indices `1,2,6,12`). -/
def fibPrimWitness : ℕ → ℕ
  | 3 => 2 | 4 => 3 | 5 => 5 | 7 => 13 | 8 => 7 | 9 => 17 | 10 => 11 | 11 => 89
  | 13 => 233 | 14 => 29 | 15 => 61 | 16 => 47 | 17 => 1597 | 18 => 19 | 19 => 37
  | 20 => 41 | 21 => 421 | 22 => 199 | 23 => 28657 | 24 => 23 | 25 => 3001
  | 26 => 521 | 27 => 53 | 28 => 281 | 29 => 514229 | 30 => 31 | 31 => 557
  | 32 => 2207 | 33 => 19801 | 34 => 3571 | 35 => 141961 | 36 => 107 | 37 => 73
  | 38 => 9349 | 39 => 135721 | 40 => 2161 | _ => 0

/-
!-- Carmichael's primitive-divisor theorem for `1 ≤ n ≤ 40`, `n ∉ {1,2,6,12}`:
the tabulated witness is a primitive divisor in every case (`native_decide`). -- !--
-/

end FibEntryDuality


