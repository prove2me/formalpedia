-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_cyclotomic_two_mul_eval_neg_one
-- name    : Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:18:59.766137+00:00
-- url     : https://prove2.me/theorems/1a7595fc-1ab4-4050-9a20-5e6fa67a2c14
-- title:
--   The local bridge.
-- statement:
--   **The local bridge.** For odd `n > 0`, evaluating the `2n`-th cyclotomic polynomial at
--   `-1` gives the same value as evaluating the `n`-th one at `1`.
--
--   The proof is a strong induction: both sides satisfy the *same* multiplicative recursion over
--   the divisor lattice of `n`, one coming from the knot side (`A_n(-1) = n`) and one from the
--   classical geometric-sum identity.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one:
--       ∀ n : ℕ, Odd n → 0 < n →
--         (cyclotomic (2 * n) ℤ).eval (-1) = (cyclotomic n ℤ).eval 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeVI.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeVI.lean#L51

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

theorem Bridges.AlexanderTorus.cyclotomic_two_mul_eval_neg_one:
    ∀ n : ℕ, Odd n → 0 < n →
      (cyclotomic (2 * n) ℤ).eval (-1) = (cyclotomic n ℤ).eval 1 := by sorry
