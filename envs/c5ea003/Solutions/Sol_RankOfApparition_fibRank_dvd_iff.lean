-- Prove2me | solution 1 for RankOfApparition.fibRank_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:10:29.776985+00:00
-- url     : https://prove2.me/submissions/9651a26d-7d71-4d3f-8252-d86689a470a0

-- Sol generated from Applications/Pythagorean/RankOfApparition.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_RankOfApparition
import Theorems.Thm_RankOfApparition_dvd_fib_fibRank
import Theorems.Thm_RankOfApparition_fibRank_min
import Theorems.Thm_RankOfApparition_fibRank_pos

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

/-! ## §3. Order-morphism law (with existence) -/

/-
!-- Lab Notebook: fibRank_dvd_of_dvd -- !--
!-- Hypothesis: `fibRank` is an order morphism of divisibility posets:
`b ∣ a → fibRank b ∣ fibRank a` (for `a > 0`). -- !--
!-- Result: Proved from the spine: `b ∣ a ∣ F (fibRank a)`, so `b ∣ F (fibRank a)`, and the
spine for `b` gives `fibRank b ∣ fibRank a`. -- !--
!-- Insight: Packages monotonicity together with existence of the rank of the divisor, so it
needs no positivity side-condition on `b` (it follows from `b ∣ a`, `0 < a`). -- !--
!-- Failure analysis: requires `0 < a` so that `a` (hence `b`) has a rank. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §4. The rank pins Fibonacci values exactly: `fibRank (F k) = k` -/

/-
!-- Lab Notebook: fibRank_fib -- !--
!-- Hypothesis: `fibRank (F k) = k` for `k ≥ 3`: a Fibonacci number's rank is its own index. -- !--
!-- Result: Proved via `Nat.find_eq_iff`: `F k ∣ F k` trivially, and for `0 < j < k` we have
`0 < F j < F k` (strict monotonicity `Nat.fib_strictMonoOn` for `j ≥ 2`, and `F 1 = F 2 = 1`
for small `j`), so `F k ∤ F j`. -- !--
!-- Insight: The rank labelling is injective on the Fibonacci numbers themselves — the
sharpest possible rigidity, absent from every catalog thread. -- !--
!-- Failure analysis: `k = 1, 2` give `F 1 = F 2 = 1` with rank `1 ≠ k`, so `k ≥ 3` is sharp. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §5. New corollary: the Fibonacci divisibility biconditional -/

/-
!-- Lab Notebook: fib_dvd_fib_iff -- !--
!-- Hypothesis: `F a ∣ F b ↔ a ∣ b` for `a ≥ 3` (Mathlib has only the forward `Nat.fib_dvd`). -- !--
!-- Result: Proved from `fibRank_fib` + spine: `F a ∣ F b ↔ fibRank (F a) ∣ b ↔ a ∣ b`. -- !--
!-- Insight: The spine converts a statement about Fibonacci numbers into a statement about
their indices, instantly upgrading `Nat.fib_dvd` to a biconditional. -- !--
!-- Failure analysis: `a = 1, 2` break it (`F 1 = F 2 = 1` divides everything), so `a ≥ 3`. -- !--
!-- End Lab Notebook -- !--
-/

/-! ## §6. Carmichael's prime case for all primes `p ≥ 3` -/


/-
!-- Lab Notebook: fib_prime_index_has_primitive -- !--
!-- Hypothesis: For every prime `p ≥ 3`, `F p` has a primitive prime divisor (Carmichael's
prime case), with the catalog's `p ≥ 5` restriction removed. -- !--
!-- Result: Proved from the spine. Take a prime divisor `q` of `F p` (which exists since
`F p ≠ 1`); it has a rank dividing `p` (spine, `q ∣ F p`). The rank is not `1` (else `q ∣ F 1 = 1`), and `p` is
prime, so the rank equals `p`; hence `q ∤ F k` for every `0 < k < p`. -- !--
!-- Insight: Primitivity at the prime index is forced purely by the rank dividing a prime —
no growth estimates, unlike the composite case. -- !--
!-- Failure analysis: `p = 3` gives `F 3 = 2`, primitive divisor `2`; the bound is sharp since
`F 1 = F 2 = 1` have no prime divisor. -- !--
!-- End Lab Notebook -- !--
-/


open RankOfApparition in
theorem solution{m : ℕ} (hm : HasFibRank m) (n : ℕ) :
    m ∣ Nat.fib n ↔ fibRank m ∣ n := by
  have hz : 0 < fibRank m := fibRank_pos hm
  have hmz : m ∣ Nat.fib (fibRank m) := dvd_fib_fibRank hm
  constructor <;> intro hn
  · contrapose! hn
    have hgcd_lt : Nat.gcd (fibRank m) n < fibRank m :=
      lt_of_le_of_ne (Nat.le_of_dvd hz (Nat.gcd_dvd_left _ _))
        (fun h => hn (h ▸ Nat.gcd_dvd_right _ _))
    refine fun hcontra => fibRank_min (Nat.gcd_pos_of_pos_left _ hz) hgcd_lt ?_
    have := Nat.dvd_gcd hmz hcontra
    simpa [Nat.fib_gcd] using this
  · obtain ⟨k, rfl⟩ := hn
    exact dvd_trans hmz (Nat.fib_dvd _ _ ⟨k, rfl⟩)
