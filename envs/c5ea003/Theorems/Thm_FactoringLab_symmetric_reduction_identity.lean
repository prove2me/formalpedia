-- Prove2me | Theorems.Thm_FactoringLab_symmetric_reduction_identity
-- name    : FactoringLab.symmetric_reduction_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:26.547467+00:00
-- url     : https://prove2.me/theorems/de8ddf90-ebf3-4dfc-8655-a1bf2d2f6a7d
-- title:
--   Symmetric reduction identity (arbitrary degree).
-- statement:
--   **Symmetric reduction identity (arbitrary degree).**  Writing
--   `B X + A` for the remainder of `F` modulo `(X − p)(X − q)`, the values of `F`
--   at the two factors are the affine values `B p + A` and `B q + A`, and their
--   product — the multiplicative invariant at the semiprime — is the universal
--   quadratic form `A² + A B (p + q) + B² (p q)` in the elementary symmetric
--   functions of the factor pair.
--
--   ```lean
--   theorem FactoringLab.symmetric_reduction_identity(F : Polynomial ℤ) (p q : ℤ) :
--       let A := (F %ₘ pairPoly p q).coeff 0
--       let B := (F %ₘ pairPoly p q).coeff 1
--       F.eval p = B * p + A ∧ F.eval q = B * q + A ∧
--         F.eval p * F.eval q = A ^ 2 + A * B * (p + q) + B ^ 2 * (p * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SymmetricReduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SymmetricReduction.lean#L70

-- Thm stub generated from Probability/SymmetricReduction.lean
import Mathlib
import Definitions.Def_Probability_QuadraticDichotomy
import Definitions.Def_Probability_SymmetricReduction
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

open FactoringLab

theorem FactoringLab.symmetric_reduction_identity(F : Polynomial ℤ) (p q : ℤ) :
    let A := (F %ₘ pairPoly p q).coeff 0
    let B := (F %ₘ pairPoly p q).coeff 1
    F.eval p = B * p + A ∧ F.eval q = B * q + A ∧
      F.eval p * F.eval q = A ^ 2 + A * B * (p + q) + B ^ 2 * (p * q) := by sorry
