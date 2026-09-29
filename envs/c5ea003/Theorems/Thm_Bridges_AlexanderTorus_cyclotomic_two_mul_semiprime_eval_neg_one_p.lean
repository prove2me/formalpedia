-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_cyclotomic_two_mul_semiprime_eval_neg_one_p
-- name    : Bridges.AlexanderTorus.cyclotomic_two_mul_semiprime_eval_neg_one_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T23:45:24.398372+00:00
-- url     : https://prove2.me/theorems/c2385c1e-a65b-4d83-9372-3c0d6d56fc48
-- title:
--   The semiprime case, recovering `cyclotomic_two_mul_semiprime_eval_neg_one` of cycle II
-- statement:
--   The semiprime case, recovering `cyclotomic_two_mul_semiprime_eval_neg_one` of cycle II
--   and extending it to *all* products of two distinct odd primes.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.cyclotomic_two_mul_semiprime_eval_neg_one'{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
--       (cyclotomic (2 * (p * q)) ℤ).eval (-1) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeVI.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeVI.lean#L116

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeVI.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
/-
# The knot–number bridge VI: the local–global factorization of the knot determinant

Cycle II of this thread computed the "local determinants" `Φ_{2d}(-1)` in two special
cases (`d` prime and `d` a product of two distinct primes) by dividing the global
determinant `A_N(-1) = N` by the other factors.  This file proves the *general* local–global
statement conjectured as `C2` in `FUTURE_DIRECTIONS.md`:

* `Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one` :
  for odd `n > 0`, `Φ_{2n}(-1) = Φ_n(1)`.  This is proved by strong induction from the two
  divisor-product identities
  `∏_{d ∣ n, d > 1} Φ_{2d} = A_n` (the knot side, cycle I) and
  `∏_{d ∣ n, d > 1} Φ_d = 1 + X + ⋯ + X^{n-1}` (the classical side),
  evaluated at `-1` and `1` respectively — both give `n`.
* `Bridges.AlexanderTorus.cyclotomic_two_mul_prime_pow_eval_neg_one` :
  `Φ_{2p^{k+1}}(-1) = p` for an odd prime `p`.
* `Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one_of_not_isPrimePow` :
  `Φ_{2d}(-1) = 1` if `d > 1` is odd and not a prime power.
* `Bridges.AlexanderTorus.knot_determinant_local_global` :
  `∏_{d ∣ N, d > 1} Φ_{2d}(-1) = N`, i.e. the determinant of `T(2,N)` is the product of the
  local determinants; combined with the two previous results, the only divisors contributing
  a nontrivial local determinant are the prime powers `p^j ∣ N`, each contributing `p`.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The two divisor-product identities, evaluated -/



/-! ## `Φ_{2n}(-1) = Φ_n(1)` for odd `n` -/


/-! ## The local determinants -/



/-! ## Consequences: the cycle II computations, generalized -/

theorem Bridges.AlexanderTorus.cyclotomic_two_mul_semiprime_eval_neg_one_p{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * (p * q)) ℤ).eval (-1) = 1 := by sorry
