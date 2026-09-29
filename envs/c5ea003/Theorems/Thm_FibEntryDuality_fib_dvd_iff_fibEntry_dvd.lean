-- Prove2me | Theorems.Thm_FibEntryDuality_fib_dvd_iff_fibEntry_dvd
-- name    : FibEntryDuality.fib_dvd_iff_fibEntry_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:48:54.673652+00:00
-- url     : https://prove2.me/theorems/e7ff9746-cbd9-4dba-a90e-ab0c6c574a18
-- title:
--   Fib dvd iff fibEntry dvd
-- statement:
--   Formal statement of `FibEntryDuality.fib_dvd_iff_fibEntry_dvd` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibEntryDuality.fib_dvd_iff_fibEntry_dvd(p n : ℕ) :
--       p ∣ Nat.fib n ↔ fibEntry p ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FibonacciEntryPointDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FibonacciEntryPointDuality.lean#L67

-- Thm stub generated from Novelty/FibonacciEntryPointDuality.lean
import Mathlib
import Definitions.Def_Novelty_FibonacciEntryPointDuality

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

open FibEntryDuality


/-
!-- If `p ∣ F a` and `p ∣ F b` then `p ∣ F (gcd a b)`, since `F (gcd a b) = gcd (F a) (F b)`. -- !--
-/

/-
!-- The master duality: `p ∣ F n` iff the entry point of `p` divides `n`.  Forward by
minimality of the entry point applied to `F (gcd n (z p)) = gcd (F n) (F (z p))`;
backward by `Nat.fib_dvd`.  Boundary `n = 0` is handled by `0 ∣ n ↔ n = 0`. -- !--
-/

theorem FibEntryDuality.fib_dvd_iff_fibEntry_dvd(p n : ℕ) :
    p ∣ Nat.fib n ↔ fibEntry p ∣ n := by sorry
