-- Prove2me | solution 1 for Korselt.korselt_561
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:28:35.274359+00:00
-- url     : https://prove2.me/submissions/c2e90145-fbf1-4f96-aa52-1484bd708f6d

-- Sol generated from Novelty/KorseltCarmichael.lean
import Mathlib
import Definitions.Def_Novelty_KorseltCarmichael

/-!
# Korselt's criterion and Carmichael numbers

Domain: Number Theory / Novelty.

A **Carmichael number** is a composite `n` that is a Fermat pseudoprime to *every* base
coprime to it: `n ∣ b ^ (n-1) - 1` for all `b` with `gcd(n,b) = 1`.  Mathlib defines
`Nat.FermatPsp` (pseudoprime to a single base) but explicitly notes that Carmichael numbers
are *"not yet defined"* (see `Mathlib/NumberTheory/FermatPsp.lean`).  This file supplies the
missing structural backbone via **Korselt's criterion** and connects it to Mathlib's
`Nat.FermatPsp`.

We package the *sufficient* half of Korselt's criterion in the predicate `Korselt`:
`n` is squarefree, composite, `> 1`, and `(p - 1) ∣ (n - 1)` for every prime `p ∣ n`.

## Main results

* `Korselt.dvd_pow_sub_self` — the heart: a squarefree `n` whose prime factors `p` all satisfy
  `(p-1) ∣ (n-1)` divides `a ^ n - a` for *every* integer `a` (Fermat's little theorem holds
  universally, not just for coprime bases).
* `Korselt.fermatPsp_of_coprime` — the bridge to Mathlib: a Korselt number is a `Nat.FermatPsp`
  to every coprime base.  This is exactly the Carmichael property.
* `Korselt.odd` — every Korselt number is odd.
* `Korselt.three_le_card_primeFactors` — every Korselt number has at least three distinct prime
  factors.
* `Korselt.korselt_561` / `Korselt.fermatPsp_561` — `561 = 3·11·17` is a Korselt number, hence a
  Carmichael number (the smallest one).

## Catalog synthesis

This extends the catalog's number-theoretic thread (the Fibonacci `gcd`-bridge `Nat.fib_gcd`
used across `Catalog/Applications/FibonacciEntryPoints.lean`, and the Fermat-pseudoprime
direction) by installing the *Korselt* backbone of Carmichael theory, a structure Mathlib
itself flags as missing.  The headline `fermatPsp_of_coprime` is a cross-domain bridge:
finite-field exponentiation in `ZMod p` (`ZMod.pow_card_sub_one_eq_one`) is glued, through the
CRT-style `Finset.prod_dvd_of_coprime` over `Nat.primeFactors`, to Mathlib's `Nat.FermatPsp`.
-/

-- !-- Lab Notebook -- !--
-- Hypothesis: Korselt's criterion (squarefree + `(p-1)∣(n-1)` for all primes `p∣n`) should be
--   formalizable from first principles and yield, for free, the full Carmichael property as a
--   bridge into Mathlib's `Nat.FermatPsp`.
-- Result: Proved the integer identity `n ∣ a^n - a` for all `a`, the bridge to `Nat.FermatPsp`,
--   oddness, the `≥ 3` prime-factor structure theorem, and the canonical instance `561`.
-- Insight: The whole edifice reduces to two clean mechanisms — (1) in each residue field
--   `ZMod p`, `x^n = x` because `(p-1)∣(n-1)`; (2) squarefreeness lets the pairwise-coprime
--   primes recombine via `Finset.prod_dvd_of_coprime`. Compositeness is never needed for the
--   Fermat identity itself; it is only needed for the structural `odd` / `≥3 factors` theorems.
-- Failure analysis: `decide` does NOT evaluate `Squarefree`, `primeFactors`, or bounded `∀ p`
--   prime statements (the `Decidable` instances get stuck on `minSqFac` / `primeFactorsList`).
--   The working route for the `561` instance is `Nat.squarefree_mul_iff` + `Nat.Prime.squarefree`
--   for squarefreeness, and `Nat.Prime.dvd_mul` peeling for the divisor enumeration.
-- !-- end -- !--

open scoped Classical

open Korselt


-- !-- In each prime residue field `ZMod p`, `x^n = x`: if `x = 0` use `n ≥ 1`; otherwise
-- !-- `x^(p-1) = 1` (Fermat) and `(p-1) ∣ (n-1)` collapse `x^(n-1)` to `1`. -- !--

-- !-- For a single prime `p ∣ n`, reduce `(p:ℤ) ∣ a^n - a` to `(↑a)^n = ↑a` in `ZMod p` via
-- !-- `ZMod.intCast_zmod_eq_zero_iff_dvd`, then apply `pow_eq_self_zmod`. -- !--

-- !-- Heart of Korselt: write the squarefree `n` as the product of its distinct (hence pairwise
-- !-- coprime) prime factors; each prime divides `a^n - a`, so the product does too via
-- !-- `Finset.prod_dvd_of_coprime`, and the product is `n`. -- !--

-- !-- Bridge to Mathlib: from `n ∣ b^n - b = b·(b^{n-1}-1)` and `gcd(n,b)=1`, cancel the coprime
-- !-- factor `b` to get the `ProbablePrime` condition `n ∣ b^{n-1} - 1`, packaging `Nat.FermatPsp`. -- !--

-- !-- If `n` were even, squarefree+composite forces an odd prime factor `p`; then `2 ∣ (p-1) ∣ (n-1)`
-- !-- makes `n-1` even, contradicting `n` even. -- !--

-- !-- A Korselt number cannot be a product of two distinct primes `p < q`: `(q-1) ∣ (n-1) = (pq-1)`
-- !-- and `pq-1 = p(q-1)+(p-1)` give `(q-1) ∣ (p-1)`, impossible since `0 < p-1 < q-1`. -- !--

-- !-- Combine: a squarefree non-prime `> 1` has `≥ 1` prime factors; `= 1` would make it prime,
-- !-- `= 2` would make it a product of two distinct primes (ruled out by `not_eq_mul_two_primes`). -- !--




open Korselt in
theorem solution: IsKorselt 561 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · -- squarefree, via distinct prime factorization
    have h : (561 : ℕ) = 3 * (11 * 17) := by norm_num
    rw [h, Nat.squarefree_mul_iff]
    refine ⟨by norm_num, (by norm_num : Nat.Prime 3).squarefree, ?_⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨by norm_num, (by norm_num : Nat.Prime 11).squarefree,
      (by norm_num : Nat.Prime 17).squarefree⟩
  · -- Korselt divisibility condition for each prime divisor
    intro p hp hpd
    have h : (561 : ℕ) = 3 * 11 * 17 := by norm_num
    rw [h] at hpd
    rcases hp.dvd_mul.mp hpd with h' | h17
    · rcases hp.dvd_mul.mp h' with h3 | h11
      · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3]; norm_num
      · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11]; norm_num
    · rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h17]; norm_num
