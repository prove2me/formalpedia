-- Prove2me | Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
-- name    : Bridges_AlexanderKnotNumberBridgeXII
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:13.71367+00:00
-- url     : https://prove2.me/theorems/d1280f4a-0675-4a39-9dbc-53249688787a
-- title:
--   Aether Catalog definitions — Bridges_AlexanderKnotNumberBridgeXII
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlexanderKnotNumberBridgeXII`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlexanderKnotNumberBridgeXII.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
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

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-- The index set of `T(r,N)`: divisors of `rN` dividing neither `r` nor `N`. -/
def torusIdx (r N : ℕ) : Finset ℕ := (r * N).divisors \ (r.divisors ∪ N.divisors)

/-- The Alexander polynomial of the torus knot `T(r,N)`, as a cyclotomic product. -/
noncomputable def torusAlexander (r N : ℕ) : ℤ[X] :=
  ∏ d ∈ torusIdx r N, cyclotomic d ℤ




/-! ## The genus formula as a divisor-lattice identity -/



/-! ## The `r = 2` slice is the bridge of cycle I -/




end Bridges.AlexanderTorus


