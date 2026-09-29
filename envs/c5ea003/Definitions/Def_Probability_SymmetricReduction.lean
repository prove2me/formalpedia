-- Prove2me | Definitions.Def_Probability_SymmetricReduction
-- name    : Probability_SymmetricReduction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:12.064809+00:00
-- url     : https://prove2.me/theorems/f76817b9-6e25-42ab-949c-2f0bd16b87bc
-- title:
--   Aether Catalog definitions — Probability_SymmetricReduction
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SymmetricReduction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SymmetricReduction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_QuadraticDichotomy
/-
# Symmetric Reduction in Arbitrary Degree (Factoring Lab, Phase A v19c — cycle 2)

The general-degree mechanism behind the multiplicative dichotomy.

`Catalog/Probability/QuadraticDichotomy.lean` proves the dichotomy for
`F(r) = a r² + b r + c` by an explicit expansion of `F(p)F(q)` in the
elementary symmetric functions `s = p + q` and `N = pq`.  That expansion is not
an accident of degree `2`: for **every** `F ∈ ℤ[X]`, reduction modulo the
minimal polynomial `(X − p)(X − q) = X² − sX + N` of the factor pair replaces
`F` by its degree-`≤ 1` remainder `B X + A`, and then

`F(p) = B p + A`,  `F(q) = B q + A`,  `F(p) F(q) = A² + A B s + B² N`.

So the value of *any* polynomial multiplicative invariant on a semiprime is the
same universal quadratic form `A² + A B s + B² N` in the symmetric data; the
degree of `F` only affects how `A` and `B` are computed.  The results are:

* `FactoringLab.symmetric_reduction_identity` — the identity above, for
  arbitrary `F` and arbitrary integers `p`, `q`;
* `FactoringLab.reduction_slope_eq_zero_iff` — the reduction slope `B` vanishes
  exactly when `F` fails to separate the two factors, `F(p) = F(q)`; this is
  the general form of the degenerate ("`N`-only") side of the dichotomy;
* `FactoringLab.symmetric_reduction_of_slope_zero` — in that case the invariant
  collapses to the perfect square `A²`;
* `FactoringLab.symmetric_reduction_determines_sum` — when `B ≠ 0` the sum
  `s = p + q` is recovered from `(N, T)` and the reduction data by a single
  division, and hence, via `FactoringLab.recovery_from_sum`, so is the
  factorization.

What is *not* claimed: `A` and `B` are here computed from `p` and `q`, not from
`N` alone.  Turning the identity into a genuine algorithmic dichotomy for every
degree requires tracking `A` and `B` as polynomials in `(N, s)`; that step is
recorded as a next-cycle sub-conjecture in `FUTURE_DIRECTIONS.md`, and is
carried out explicitly for degree `≤ 2` in `QuadraticDichotomy.lean`.
-/

open Polynomial

namespace FactoringLab

/-- The minimal polynomial of the factor pair: `(X − p)(X − q) = X² − sX + N`. -/
noncomputable def pairPoly (p q : ℤ) : Polynomial ℤ := (X - C p) * (X - C q)











end FactoringLab


