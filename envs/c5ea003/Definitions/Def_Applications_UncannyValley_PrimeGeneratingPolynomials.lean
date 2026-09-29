-- Prove2me | Definitions.Def_Applications_UncannyValley_PrimeGeneratingPolynomials
-- name    : Applications_UncannyValley_PrimeGeneratingPolynomials
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:23.133102+00:00
-- url     : https://prove2.me/theorems/9f923c65-c814-4e52-8275-190b3414d3d1
-- title:
--   Aether Catalog definitions — Applications_UncannyValley_PrimeGeneratingPolynomials
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.UncannyValley.PrimeGeneratingPolynomials`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/UncannyValley/PrimeGeneratingPolynomials.lean by skeleton subtraction
import Mathlib

/-!
# The Uncanny Valley of Prime-Generating Formulas

A recurring illusion in number theory is the *prime-generating polynomial*: a
simple algebraic expression that produces a long, unbroken run of primes and
therefore *looks* like a formula for the primes.  The most famous example is
Euler's polynomial `n² + n + 41`, which is prime for every one of the forty
inputs `n = 0, 1, …, 39`.  A formula this accurate is squarely in the *uncanny
valley*: it is almost, but not quite, a genuine prime formula.

This file explains *why* every such formula must eventually fail.  The central
result is a clean structural obstruction:

* `UncannyValley.no_prime_generating_polynomial` — **no nonconstant integer
  polynomial takes a prime value at every integer input.**

The proof turns on the divisibility identity `f(a) ∣ f(a + k·f(a))`, isolated as
`UncannyValley.eval_dvd_eval_shift`.  If `f(a) = p` is prime, then `p` divides
`f(a + k·p)` for *every* `k`; since each of those values is itself prime, they
are all forced into the two-element set `{p, -p}`.  An infinite family of inputs
mapping into a finite set of values would make `f` constant, a contradiction.

We then return to the motivating example and exhibit both faces of the uncanny
valley for Euler's polynomial:

* `UncannyValley.euler_prime_run` — it is prime for all `n = 0, …, 39`;
* `UncannyValley.euler_not_prime_at_40` — it fails at the very next input,
  where `40² + 40 + 41 = 41²`;
* `UncannyValley.euler_polynomial_not_prime_generating` — the general theorem,
  specialised to Euler's polynomial, guarantees a failure must exist.
-/

namespace UncannyValley

open Polynomial




/-
**Strengthening — the valley has infinite width.**  A nonconstant integer
polynomial is not merely doomed to fail somewhere: it takes a non-prime value at
*infinitely many* integer inputs.  No matter how the formula is tuned, the set of
inputs on which the prime illusion breaks is infinite.
-/

/-! ### Euler's polynomial `n² + n + 41` — a tour of the uncanny valley -/

/-- Euler's celebrated prime-generating polynomial, as an integer polynomial. -/
noncomputable def eulerPoly : ℤ[X] := X ^ 2 + X + C 41






end UncannyValley


