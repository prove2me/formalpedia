-- Prove2me | Definitions.Def_Applications_ThreeSumFactoring
-- name    : Applications_ThreeSumFactoring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:36:23.623202+00:00
-- url     : https://prove2.me/theorems/4e2d1019-9728-497a-acae-42cea9f011c4
-- title:
--   Aether Catalog definitions — Applications_ThreeSumFactoring
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ThreeSumFactoring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ThreeSumFactoring.lean by skeleton subtraction
import Mathlib
/-
# 3SUM mod `p` reveals a factor of `N = p*q`

Let `N = p * q` be a semiprime with `p ≠ q` two primes.  If a triple `(a,b,c)`
satisfies

* `a + b + c ≡ 0 (mod p)`, and
* `a + b + c ≢ 0 (mod q)`,

then `gcd(a+b+c, N) = p`: the triple *reveals* the factor `p`.

The file proves the general gcd lemma behind this observation, the 3SUM
specialisation, and a *guaranteed reveal* theorem which explains the experimental
observation that no small triple is ever divisible by both primes: any positive
sum smaller than `N` that is divisible by `p` is automatically **not** divisible
by `q`, hence always reveals `p`.  A concrete `N = 143 = 11 * 13` census is
verified by kernel computation.

Companion file: `Catalog/Applications/BirthdayBoundHierarchy.lean`, which shows
that the *cost* of finding such a triple obeys the same `√N` barrier as every
other collision-based factoring method.
-/

namespace ThreeSumFactoring

/-! ## The core arithmetic lemma -/



/-! ## The 3SUM specialisation -/





/-! ## Concrete census for `N = 143 = 11 * 13` -/

/-- Strictly increasing triples from `{1,…,12}` whose sum vanishes mod `11`. -/
def triples143 : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 12) ×ˢ (Finset.Icc 1 12) ×ˢ (Finset.Icc 1 12)).filter
    (fun t => t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ 11 ∣ (t.1 + t.2.1 + t.2.2))




end ThreeSumFactoring


