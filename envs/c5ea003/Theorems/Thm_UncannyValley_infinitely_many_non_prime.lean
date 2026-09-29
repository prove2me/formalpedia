-- Prove2me | Theorems.Thm_UncannyValley_infinitely_many_non_prime
-- name    : UncannyValley.infinitely_many_non_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:07:04.201745+00:00
-- url     : https://prove2.me/theorems/3f6a13c9-dede-4a7a-afd1-30a8b3aac837
-- title:
--   Infinitely many non prime
-- statement:
--   Formal statement of `UncannyValley.infinitely_many_non_prime` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem UncannyValley.infinitely_many_non_prime(f : ℤ[X]) (hnonconst : ∀ c : ℤ, f ≠ C c) :
--       {n : ℤ | ¬ Prime (f.eval n)}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/UncannyValley/PrimeGeneratingPolynomials.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/UncannyValley/PrimeGeneratingPolynomials.lean#L82

-- Thm stub generated from Applications/UncannyValley/PrimeGeneratingPolynomials.lean
import Mathlib
import Definitions.Def_Applications_UncannyValley_PrimeGeneratingPolynomials

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

open UncannyValley

open Polynomial




/-
**Strengthening — the valley has infinite width.**  A nonconstant integer
polynomial is not merely doomed to fail somewhere: it takes a non-prime value at
*infinitely many* integer inputs.  No matter how the formula is tuned, the set of
inputs on which the prime illusion breaks is infinite.
-/

theorem UncannyValley.infinitely_many_non_prime(f : ℤ[X]) (hnonconst : ∀ c : ℤ, f ≠ C c) :
    {n : ℤ | ¬ Prime (f.eval n)}.Infinite := by sorry
