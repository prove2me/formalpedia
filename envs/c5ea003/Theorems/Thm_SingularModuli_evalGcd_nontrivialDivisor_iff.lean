-- Prove2me | Theorems.Thm_SingularModuli_evalGcd_nontrivialDivisor_iff
-- name    : SingularModuli.evalGcd_nontrivialDivisor_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:03:48.005624+00:00
-- url     : https://prove2.me/theorems/b785e87e-4ca9-4b96-933a-09c585ddd98e
-- title:
--   The exact success criterion for the singular moduli gcd step.
-- statement:
--   **The exact success criterion for the singular moduli gcd step.**
--   For a semiprime `N = p q` with distinct primes, the evaluation point `j`
--   produces a nontrivial factor of `N` if and only if `j` is a root of `H` modulo
--   exactly one of `p` and `q`.
--
--   ```lean
--   theorem SingularModuli.evalGcd_nontrivialDivisor_iff(hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
--       NontrivialDivisor (p * q) (evalGcd H j (p * q)) ↔
--         Xor ((p : ℤ) ∣ H.eval j) ((q : ℤ) ∣ H.eval j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/GcdCriterion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/GcdCriterion.lean#L116

-- Thm stub generated from Cryptography/SingularModuli/GcdCriterion.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion

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

open SingularModuli

open Polynomial FactoringBarriers


variable {p q : ℕ} {H : Polynomial ℤ} {j : ℤ}

theorem SingularModuli.evalGcd_nontrivialDivisor_iff(hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    NontrivialDivisor (p * q) (evalGcd H j (p * q)) ↔
      Xor ((p : ℤ) ∣ H.eval j) ((q : ℤ) ∣ H.eval j) := by sorry
