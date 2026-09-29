-- Prove2me | solution 1 for FactoringLab.symmetric_reduction_determines_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:58:53.330007+00:00
-- url     : https://prove2.me/submissions/87530eb6-96e4-48e4-9ff5-c7d740763b52

-- Sol generated from Probability/SymmetricReduction.lean
import Mathlib
import Definitions.Def_Probability_QuadraticDichotomy
import Definitions.Def_Probability_SymmetricReduction
import Theorems.Thm_FactoringLab_recovery_from_sum
import Theorems.Thm_FactoringLab_symmetric_reduction_identity
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













open FactoringLab in
theorem solution(F : Polynomial ℤ) {p q : ℤ} (hpq : p ≤ q)
    (hA : (F %ₘ pairPoly p q).coeff 0 ≠ 0)
    (hB : (F %ₘ pairPoly p q).coeff 1 ≠ 0) :
    let A := (F %ₘ pairPoly p q).coeff 0
    let B := (F %ₘ pairPoly p q).coeff 1
    let N := p * q
    let T := F.eval p * F.eval q
    let s := (T - A ^ 2 - B ^ 2 * N) / (A * B)
    s = p + q ∧
      (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
      (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by
  intro A B N T s
  obtain ⟨-, -, hprod⟩ := symmetric_reduction_identity F p q
  have hAB : A * B ≠ 0 := mul_ne_zero hA hB
  have hs : s = p + q := by
    have hnum : T - A ^ 2 - B ^ 2 * N = A * B * (p + q) := by
      simp only [T, N]
      rw [hprod]
      ring
    simp only [s, hnum]
    exact Int.mul_ediv_cancel_left _ hAB
  obtain ⟨-, h1, h2⟩ := recovery_from_sum hpq (rfl : N = p * q) hs
  exact ⟨hs, h1, h2⟩
