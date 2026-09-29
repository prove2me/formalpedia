-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_torusAlexander_defining_identity
-- name    : Bridges.AlexanderTorus.torusAlexander_defining_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:19:08.172461+00:00
-- url     : https://prove2.me/theorems/ce181dcc-5ce8-441b-81d6-cdd579ba48d3
-- title:
--   The defining identity of the torus-knot Alexander polynomial.
-- statement:
--   **The defining identity of the torus-knot Alexander polynomial.**  For coprime `r, N > 0`,
--   `(X^{rN} − 1)(X − 1) = (X^r − 1)(X^N − 1) · ∏_{d ∣ rN, d ∤ r, d ∤ N} Φ_d`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.torusAlexander_defining_identity{r N : ℕ} (hco : Nat.Coprime r N)
--       (hr : 0 < r) (hN : 0 < N) :
--       ((X : ℤ[X]) ^ (r * N) - 1) * ((X : ℤ[X]) - 1)
--         = ((X : ℤ[X]) ^ r - 1) * ((X : ℤ[X]) ^ N - 1) * torusAlexander r N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeXII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeXII.lean#L53

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeXII.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
/-
# The knot–number bridge XII: the two-parameter family `T(r,N)`

Conjecture `D4` of `FUTURE_DIRECTIONS.md` predicted that the whole bridge is a shadow of a
two-parameter statement: for coprime `r, N` the Alexander polynomial of the torus knot
`T(r,N)`, characterised by

  `(X^{rN} − 1)(X − 1) = (X^r − 1)(X^N − 1) · A_{r,N}(X)`,

should be the cyclotomic product over the divisors of `rN` that divide neither `r` nor `N`.
This file proves it, and identifies the `r = 2` case with the `alexander N` of cycle I.

* `Bridges.AlexanderTorus.torusAlexander` : `∏_{d ∣ rN, d ∤ r, d ∤ N} Φ_d`;
* `Bridges.AlexanderTorus.torusAlexander_defining_identity` : it satisfies the defining
  identity above (so it *is* the Alexander polynomial of `T(r,N)`), for coprime `r, N > 0`;
* `Bridges.AlexanderTorus.torusAlexander_natDegree` : its degree is `(r−1)(N−1)`, the
  classical genus formula `2g = (r−1)(N−1)`, obtained here purely from `∑_{d ∣ n} φ(d) = n`
  and inclusion–exclusion on the divisor lattice;
* `Bridges.AlexanderTorus.torusAlexander_two_eq_alexander` : for odd `N > 0`,
  `A_{2,N} = A_N`, so cycle I's bridge is the `r = 2` slice;
* `Bridges.AlexanderTorus.torusAlexander_semiprime_natDegree_factors` : the degrees of the
  cyclotomic factors of `A_{r,N}` again read off the arithmetic of `rN` — for distinct odd
  primes `p, q` and `r = p`, `N = q` the polynomial `A_{p,q} = Φ_{pq}` has degree
  `(p−1)(q−1) = φ(pq)`.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

theorem Bridges.AlexanderTorus.torusAlexander_defining_identity{r N : ℕ} (hco : Nat.Coprime r N)
    (hr : 0 < r) (hN : 0 < N) :
    ((X : ℤ[X]) ^ (r * N) - 1) * ((X : ℤ[X]) - 1)
      = ((X : ℤ[X]) ^ r - 1) * ((X : ℤ[X]) ^ N - 1) * torusAlexander r N := by sorry
