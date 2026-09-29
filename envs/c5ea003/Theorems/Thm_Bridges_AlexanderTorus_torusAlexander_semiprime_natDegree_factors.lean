-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_torusAlexander_semiprime_natDegree_factors
-- name    : Bridges.AlexanderTorus.torusAlexander_semiprime_natDegree_factors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:19:14.852514+00:00
-- url     : https://prove2.me/theorems/94e4f185-33cb-44b3-9e67-fb204836bf84
-- title:
--   The semiprime slice of the two-parameter family: for distinct primes `p ≠ q`,
-- statement:
--   The semiprime slice of the two-parameter family: for distinct primes `p ≠ q`,
--   `A_{p,q} = Φ_{pq}`, of degree `(p−1)(q−1) = φ(pq)`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.torusAlexander_semiprime_natDegree_factors{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hne : p ≠ q) :
--       torusAlexander p q = cyclotomic (p * q) ℤ ∧
--         (torusAlexander p q).natDegree = (p - 1) * (q - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeXII.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeXII.lean#L148

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






/-! ## The genus formula as a divisor-lattice identity -/



/-! ## The `r = 2` slice is the bridge of cycle I -/

theorem Bridges.AlexanderTorus.torusAlexander_semiprime_natDegree_factors{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    torusAlexander p q = cyclotomic (p * q) ℤ ∧
      (torusAlexander p q).natDegree = (p - 1) * (q - 1) := by sorry
