-- Prove2me | Theorems.Thm_FactoringLab_symmetric_reduction_determines_sum
-- name    : FactoringLab.symmetric_reduction_determines_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:51.947056+00:00
-- url     : https://prove2.me/theorems/b2a640ec-6660-463a-ac18-fece1c1ecf25
-- title:
--   Recovery side, arbitrary degree: a nonzero reduction slope makes the sum
-- statement:
--   Recovery side, arbitrary degree: a nonzero reduction slope makes the sum
--   `p + q` an explicit quotient of the invariant value by the reduction data, and
--   therefore — through `recovery_from_sum` — yields the factorization in closed
--   form.
--
--   ```lean
--   theorem FactoringLab.symmetric_reduction_determines_sum(F : Polynomial ℤ) {p q : ℤ} (hpq : p ≤ q)
--       (hA : (F %ₘ pairPoly p q).coeff 0 ≠ 0)
--       (hB : (F %ₘ pairPoly p q).coeff 1 ≠ 0) :
--       let A := (F %ₘ pairPoly p q).coeff 0
--       let B := (F %ₘ pairPoly p q).coeff 1
--       let N := p * q
--       let T := F.eval p * F.eval q
--       let s := (T - A ^ 2 - B ^ 2 * N) / (A * B)
--       s = p + q ∧
--         (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
--         (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SymmetricReduction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SymmetricReduction.lean#L121

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

theorem FactoringLab.symmetric_reduction_determines_sum(F : Polynomial ℤ) {p q : ℤ} (hpq : p ≤ q)
    (hA : (F %ₘ pairPoly p q).coeff 0 ≠ 0)
    (hB : (F %ₘ pairPoly p q).coeff 1 ≠ 0) :
    let A := (F %ₘ pairPoly p q).coeff 0
    let B := (F %ₘ pairPoly p q).coeff 1
    let N := p * q
    let T := F.eval p * F.eval q
    let s := (T - A ^ 2 - B ^ 2 * N) / (A * B)
    s = p + q ∧
      (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
      (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by sorry
