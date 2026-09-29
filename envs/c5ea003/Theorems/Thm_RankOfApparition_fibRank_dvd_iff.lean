-- Prove2me | Theorems.Thm_RankOfApparition_fibRank_dvd_iff
-- name    : RankOfApparition.fibRank_dvd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:01:41.392311+00:00
-- url     : https://prove2.me/theorems/07bbc272-0fa3-47bf-b5fb-9d424b7fbfa4
-- title:
--   FibRank dvd iff
-- statement:
--   Formal statement of `RankOfApparition.fibRank_dvd_iff` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RankOfApparition.fibRank_dvd_iff{m : ℕ} (hm : HasFibRank m) (n : ℕ) :
--       m ∣ Nat.fib n ↔ fibRank m ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Pythagorean/RankOfApparition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Pythagorean/RankOfApparition.lean#L136

-- Thm stub generated from Applications/Pythagorean/RankOfApparition.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_RankOfApparition

/-! # The rank of apparition as the spine of Fibonacci primitive-divisor theory

Domain: Number Theory / Applications (Bridges).

The *rank of apparition* (Fibonacci entry point) of a modulus `m` is the least positive
index `k` with `m ∣ F k`.  The catalog already contains several **parallel** developments of
this object, each turning on the same biconditional `m ∣ F n ↔ rank ∣ n`:

* `Catalog/Novelty/FibApparitionExistence.lean`
  (`FibApparition.apparitionRank`, `fib_apparition_exists`, `fib_dvd_iff_apparitionRank_dvd`);
* `Catalog/Applications/FibonacciEntryPoints.lean`
  (`FibonacciEntryPoints.entryPoint`, `dvd_fib_iff_entry_dvd`, `primitive_iff_entry_eq`);
* `Catalog/Applications/FibonacciApparitionLattice.lean`
  (`fibEntry_lcm`, `fibEntry_monotone`, `fibEntry_gcd_dvd`);
* `Catalog/Applications/FibonacciPrimitiveDivisors.lean`
  (`dvd_fib_iff_index_dvd_of_primitive`, `simultaneous_apparition`);
* `Catalog/Applications/StrongDivisibilitySequences.lean`
  (`IsStrongDivSeq`, `dvd_iff_index_dvd_of_primitive`, `apparition_count`);
* `Catalog/Algebra/Tropical_p_adic_..._Fibonacci_Primitive_Divisors.lean`
  (`fib_prime_has_primitive` for primes `p ≥ 5`).

This file is **self-contained against Mathlib** (the catalog's `import` graph is currently
fragmented, so we restate the short existence/biconditional core rather than depend on a
non-default build target), and it adds the results the parallel threads were missing:

* `fibRank_fib`            — *new*: `fibRank (F k) = k` for `k ≥ 3`.  The rank pins the
  Fibonacci values **exactly**; not present anywhere in the catalog or in Mathlib.
* `fib_dvd_fib_iff`        — *new corollary*: `F a ∣ F b ↔ a ∣ b` for `a ≥ 3`.  Mathlib has
  only the forward implication `Nat.fib_dvd`; the biconditional is absent (`exact?` fails).
* `fib_prime_index_has_primitive` — Carmichael's prime case for **all** primes `p ≥ 3`
  (the catalog's `fib_prime_has_primitive` requires `p ≥ 5`), derived in a few lines from the
  spine: the chosen prime divisor of `F p` has rank exactly `p`.
* `fibRank_dvd_of_dvd`     — the order-morphism law packaged with existence:
  `b ∣ a → 0 < a → fibRank b ∣ fibRank a`.

The reusable core (`hasFibRank_of_pos`, `fibRank_dvd_iff`) is stated *without* any
primitivity hypothesis, generalizing `FibonacciPrimitiveDivisors.dvd_fib_iff_index_dvd_of_primitive`.
-/

open RankOfApparition

open scoped Classical


/-! ## §0. Existence of the rank (pigeonhole on the Fibonacci shift) -/


-- !-- Iterating the shift from `(0,1)` yields consecutive Fibonacci pairs; induction on `k`
-- using `F (k+2) = F k + F (k+1)`. -- !--

/-
!-- Lab Notebook: hasFibRank_of_pos -- !--
!-- Hypothesis: Every positive modulus has a rank of apparition (apparition is total). -- !--
!-- Result: Proved by pigeonhole on the finite set `(ZMod m)²`: two indices `i < j` share
the pair `(F·, F·₊₁) mod m`; back-stepping `i` to `0` via the reversible shift produces a
positive `k = j - i` with `m ∣ F k`. -- !--
!-- Insight: Reversibility of the Fibonacci shift (a unit determinant matrix over `ZMod m`)
is the abstract Pisano-period mechanism; Mathlib has no Pisano theory, so this is built here. -- !--
!-- Failure analysis: the `m = 0` degenerate `ZMod` case must be split off (`cases m`). -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §1. The rank function and its defining properties -/





/-! ## §2. The spine: `m ∣ F n ↔ fibRank m ∣ n` -/

/-
!-- Lab Notebook: fibRank_dvd_iff -- !--
!-- Hypothesis: For any modulus with a rank, `m ∣ F n ↔ fibRank m ∣ n`. -- !--
!-- Result: Proved with NO primitivity hypothesis (generalizing the catalog's
`dvd_fib_iff_index_dvd_of_primitive`). (←) `fibRank m ∣ n → F (fibRank m) ∣ F n` (`Nat.fib_dvd`)
and `m ∣ F (fibRank m)`. (→) push `m` into `F (gcd (fibRank m) n) = gcd (F …) (F n)`
(`Nat.fib_gcd`); minimality of the rank forces `gcd (fibRank m) n = fibRank m`, i.e. divisibility. -- !--
!-- Insight: This single biconditional is the load-bearing fact behind every parallel
apparition thread in the catalog; dropping primitivity makes it the genuine spine. -- !--
!-- Failure analysis: needs `HasFibRank m` so the rank is positive; for `m = 0` it is vacuous. -- !--
!-- End Lab Notebook -- !--
-/

theorem RankOfApparition.fibRank_dvd_iff{m : ℕ} (hm : HasFibRank m) (n : ℕ) :
    m ∣ Nat.fib n ↔ fibRank m ∣ n := by sorry
