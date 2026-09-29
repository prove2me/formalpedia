-- Prove2me | Definitions.Def_Cryptography_SingularModuli_GcdCriterion
-- name    : Cryptography_SingularModuli_GcdCriterion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T15:41:16.160593+00:00
-- url     : https://prove2.me/theorems/789b099f-56d6-4ff3-b81f-ab3ae94754ba
-- title:
--   Aether Catalog definitions — Cryptography_SingularModuli_GcdCriterion
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SingularModuli.GcdCriterion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SingularModuli/GcdCriterion.lean by skeleton subtraction
import Mathlib

/-!
# Singular Moduli Factoring, Step 1: the exact gcd criterion

The *singular moduli* factoring method attacks a semiprime `N = p q` by picking a
discriminant `D`, forming the Hilbert class polynomial `H_D ∈ ℤ[X]` (of degree
`h = h(D)`, the class number), choosing an evaluation point `j₀ ∈ ℤ`, and
computing

  `gcd (H_D(j₀), N)`.

Heuristically this works because `j₀` "is a singular modulus mod `p`" exactly
when `H_D(j₀) ≡ 0 (mod p)`, and the elliptic curve with that `j`-invariant has
CM by the order of discriminant `D`.

This file isolates the *unconditional arithmetic core* of the method, with no
elliptic curves involved: for a semiprime `N = pq` the gcd step returns a
nontrivial factor **iff** `j₀` is a root of `H_D` modulo exactly one of the two
primes, and in that case it returns exactly that prime.  The proof is a
prime-divisor analysis of `gcd (a, pq)` and is completely general in the
polynomial `H`, so it applies verbatim to any "evaluate a fixed integer
polynomial and take a gcd" method.

Main results:

* `evalGcd_eq_one_of_no_root`   — no root: the step returns `1`;
* `evalGcd_eq_left/right`       — root mod exactly one prime: the step returns
  that prime;
* `evalGcd_eq_modulus`          — root mod both primes: the step returns `N`;
* `evalGcd_nontrivialDivisor_iff` — the exact success criterion, an `Xor`;
* `singularModuli_blind_of_no_roots` — the failure mode: if `H` has no root
  modulo either prime, *every* evaluation point is useless.
-/

namespace SingularModuli

open Polynomial

/-- One step of the singular moduli method: evaluate the integer polynomial `H`
at `j` and take the gcd with the modulus `N`. -/
def evalGcd (H : Polynomial ℤ) (j : ℤ) (N : ℕ) : ℕ := Int.gcd (H.eval j) (N : ℤ)

variable {p q : ℕ} {H : Polynomial ℤ} {j : ℤ}









end SingularModuli


