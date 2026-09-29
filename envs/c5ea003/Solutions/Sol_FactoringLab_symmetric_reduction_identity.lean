-- Prove2me | solution 1 for FactoringLab.symmetric_reduction_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:40.518228+00:00
-- url     : https://prove2.me/submissions/8b32db30-d7d8-4e72-a0b0-4f09b3b1efc2

-- Sol generated from Probability/SymmetricReduction.lean
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


theorem pairPoly_monic (p q : ℤ) : (pairPoly p q).Monic :=
  (monic_X_sub_C p).mul (monic_X_sub_C q)

theorem pairPoly_degree (p q : ℤ) : (pairPoly p q).degree = 2 := by
  unfold pairPoly
  rw [degree_mul, degree_X_sub_C, degree_X_sub_C]
  rfl

theorem pairPoly_eval_left (p q : ℤ) : (pairPoly p q).eval p = 0 := by
  simp [pairPoly]

theorem pairPoly_eval_right (p q : ℤ) : (pairPoly p q).eval q = 0 := by
  simp [pairPoly]

/-- The remainder of `F` modulo the pair polynomial is affine: `B X + A`. -/
theorem modByMonic_pairPoly_eq (F : Polynomial ℤ) (p q : ℤ) :
    F %ₘ pairPoly p q
      = C ((F %ₘ pairPoly p q).coeff 1) * X + C ((F %ₘ pairPoly p q).coeff 0) := by
  refine eq_X_add_C_of_degree_le_one ?_
  have hlt : (F %ₘ pairPoly p q).degree < (pairPoly p q).degree :=
    degree_modByMonic_lt F (pairPoly_monic p q)
  rw [pairPoly_degree] at hlt
  exact Order.le_of_lt_succ hlt







open FactoringLab in
theorem solution(F : Polynomial ℤ) (p q : ℤ) :
    let A := (F %ₘ pairPoly p q).coeff 0
    let B := (F %ₘ pairPoly p q).coeff 1
    F.eval p = B * p + A ∧ F.eval q = B * q + A ∧
      F.eval p * F.eval q = A ^ 2 + A * B * (p + q) + B ^ 2 * (p * q) := by
  intro A B
  have hdecomp : F %ₘ pairPoly p q + pairPoly p q * (F /ₘ pairPoly p q) = F :=
    modByMonic_add_div F (pairPoly p q)
  have hrem : F %ₘ pairPoly p q = C B * X + C A := modByMonic_pairPoly_eq F p q
  have hp : F.eval p = B * p + A := by
    conv_lhs => rw [← hdecomp]
    rw [eval_add, eval_mul, pairPoly_eval_left, zero_mul, add_zero, hrem]
    simp
  have hq : F.eval q = B * q + A := by
    conv_lhs => rw [← hdecomp]
    rw [eval_add, eval_mul, pairPoly_eval_right, zero_mul, add_zero, hrem]
    simp
  refine ⟨hp, hq, ?_⟩
  rw [hp, hq]; ring
