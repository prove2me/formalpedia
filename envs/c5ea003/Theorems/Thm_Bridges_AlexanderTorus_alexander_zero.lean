-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_zero
-- name    : Bridges.AlexanderTorus.alexander_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:16:04.8134+00:00
-- url     : https://prove2.me/theorems/f00d070d-d138-4c30-959f-03fa70046a2d
-- title:
--   Alexander zero
-- statement:
--   Formal statement of `Bridges.AlexanderTorus.alexander_zero` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_zero: alexander 0 = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridge.lean#L44

-- Thm stub generated from Bridges/AlexanderKnotNumberBridge.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
/-
# A Knot–Number Theory Bridge: the Alexander polynomial of the torus knot `T(2,N)`

The Alexander polynomial of the `(2,N)` torus knot is (up to normalization)

  `A_N(X) = (X^N + 1) / (X + 1) = ∑_{i < N} (-1)^i X^i`   (`N` odd).

This file proves that `A_N` is, over `ℤ`, the product of the cyclotomic polynomials
`Φ_{2d}` for the divisors `d > 1` of `N`; in particular the *multiset of degrees of
its irreducible factors* is `{φ(d) : d ∣ N, d > 1}`, which for a semiprime `N = pq`
is `{p-1, q-1, (p-1)(q-1)}`, from which `φ(N)`, `p+q` and finally `p, q` are recovered.

Main results:

* `Bridges.AlexanderTorus.prod_cyclotomic_two_mul_divisors` :
  `∏_{d ∣ N} Φ_{2d} = X^N + 1` for odd `N > 0`.
* `Bridges.AlexanderTorus.alexander_eq_prod_cyclotomic` :
  `A_N = ∏_{d ∣ N, d ≠ 1} Φ_{2d}`.
* `Bridges.AlexanderTorus.alexander_semiprime_factorization` :
  `A_{pq} = Φ_{2p} · Φ_{2q} · Φ_{2pq}` for distinct odd primes `p ≠ q`, together with
  `alexander_semiprime_factor_data`: irreducibility of the three factors and their
  degrees `p-1`, `q-1`, `(p-1)(q-1)`.
* `Bridges.AlexanderTorus.alexander_irreducible_iff_prime` :
  for odd `N > 1`, `A_N` is irreducible over `ℤ` **iff** `N` is prime.
* `Bridges.AlexanderTorus.recover_factors_from_degrees` :
  the two primes are recovered from the degree data by
  `p = (s - √(s² - 4N))/2`, `q = (s + √(s² - 4N))/2` with `s = N + 1 - φ(N)`.
* `Bridges.AlexanderTorus.knot_determinant` : `A_N(-1) = N`
  (the determinant of the torus knot `T(2,N)`), and
  `alexander_natDegree` : `deg A_N = N - 1` (the "catch": exponential size in `log N`).
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The Alexander polynomial of `T(2,N)` -/


@[simp]

theorem Bridges.AlexanderTorus.alexander_zero: alexander 0 = 0 := by sorry
