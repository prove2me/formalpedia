-- Prove2me | solution 1 for MoonshineHeadTable.headCoeff_pmFrame_two_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:52:45.657543+00:00
-- url     : https://prove2.me/submissions/cc692819-cdb2-4460-9b8b-4af676ec426c

-- Sol generated from NumberTheory/MoonshineHeadTable.lean
import Mathlib
import Definitions.Def_NumberTheory_MoonshineHeadTable

/-!
# Head coefficients of eta-quotient McKay–Thompson series, from frame shapes

This file is cycle 3 of the research thread begun in `Shared.PoleOrderObstruction`
and continued in `Shared.PoleOrderObstructionDeep`.  Those files reduced the
"Monster-sized product" of the `194` McKay–Thompson series to a *finite* piece of
arithmetic: the Laurent coefficients just above the pole are elementary symmetric
expressions in the tabulated numbers `c_g(1)`.

The obvious next question is: **where does the table `c_g(1)` come from?**  For a
large family of Monster classes the McKay–Thompson series is (up to an additive
constant) a Dedekind eta quotient

`T_g(τ) = 1 / η_g(τ) + const`,  `η_g(τ) = ∏_k η(k τ) ^ (a k)`,

attached to the *frame shape* `∏ k ^ (a k)` of `g` acting on the Leech lattice
(a balanced frame shape: `∑ k * a k = 24`).  For such `g` the head coefficient
`c_g(1)` is therefore **not tabulated data at all**: it is computable from the
finitely many integers `a k`.

The main theorem of this file, `MoonshineHeadTable.coeff_two_etaPartial`, computes
the relevant coefficient of the `q`-expansion of `1/η_g` purely formally, and gives
the closed formula

`c_g(1) = a 1 * (a 1 + 3) / 2 + a 2`.

Contents.

* `MoonshineHeadTable.coeff_one_prod_one`, `MoonshineHeadTable.two_mul_coeff_two_prod_one`
  — Newton-type identities for the linear and quadratic coefficients of a finite
  product of power series with constant term `1`, over an arbitrary commutative
  ring (the `ℂ`-versions live in `Shared.PoleOrderObstructionDeep`).
* `MoonshineHeadTable.jet_zpow` — the `2`-jet of an *integer* power `u ^ z` of a
  unit power series with constant term `1`.  This is what makes eta *quotients*
  (negative exponents) accessible.
* `MoonshineHeadTable.etaPartial` — the truncated eta-quotient unit
  `∏_{m ≤ M} (1 - qᵐ) ^ (-∑_{k ∣ m} a k)`, i.e. `q · (1/η_g)` truncated after the
  `M`-th factor.
* `MoonshineHeadTable.coeff_one_etaPartial`, `MoonshineHeadTable.coeff_two_etaPartial`
  — its linear and quadratic coefficients, *stable in `M`*
  (`MoonshineHeadTable.coeff_two_etaPartial_stable`), so that they are honest
  coefficients of the infinite product.
* `MoonshineHeadTable.headCoeff`, `MoonshineHeadTable.headCoeff_pmFrame` — the
  closed formula, and its evaluation on the family of balanced frame shapes
  `1^(-e) n^(e)` with `e * (n - 1) = 24`.
* `MoonshineHeadTable.etaHeadTable` — the resulting *derived* (not recalled) table
  of eight head coefficients `276, 54, 20, 9, 2, 0, -1, -1`, checked by `decide`,
  together with its sum `359`.

Everything is proved from scratch over a general commutative ring and specialized
to `ℤ`, where the resulting statements are decidable.
-/

open MoonshineHeadTable

open PowerSeries Finset

/-! ## 1. Newton identities for low coefficients of products, over any ring -/


variable {R : Type*} [CommRing R] {ι : Type*}





/-! ## 2. The `2`-jet of an integer power of a unit power series -/




/-! ## 3. Truncated eta quotients attached to a frame shape -/


variable (R : Type*) [CommRing R]


variable {R}



















/-! ## 4. The closed formula for the head coefficient -/





/-! ## 5. The balanced frame shapes `1^(-e) n^(e)` and the derived head table -/



theorem headCoeff_pmFrame_two (e : ℤ) : headCoeff (pmFrame 2 e) = e * (e - 3) / 2 + e := by
  have h1 : pmFrame 2 e 1 = -e := by simp [pmFrame]
  have h2 : pmFrame 2 e 2 = e := by simp [pmFrame]
  rw [headCoeff, h1, h2, show -e * (-e + 3) = e * (e - 3) by ring]






/-! ## 6. A structural constraint on the derived head coefficients

The closed formula lets us prove a *uniform* lower bound for the whole family of
balanced frame shapes `1^(-e) n^(e)`, with no case analysis on the eight admissible
pairs: the head coefficient is never smaller than `-1`.  The bound is attained
(at `e = 1` and `e = 2`, i.e. `n = 25` and `n = 13`), so it is sharp.  This is a
small, provable shadow of the positivity phenomena of Monstrous Moonshine. -/





/-!
## Lab notes (experimental data behind the formalization)

Exact-integer expansions of `q · (η(τ)/η(nτ))^e = ∏_{m ≥ 1} (1 - q^m)^(-b m)` for the
eight balanced shapes `1^(-e) n^(e)` with `e (n - 1) = 24`, truncated at `q⁴`, computed
before the proof was written and reproduced by `coeff_two_etaPartial`:

```
n= 2, e=24 : 1 - 24q + 276q² - 2048q³ + 11202q⁴     c(1) = 276
n= 3, e=12 : 1 - 12q +  54q² -   76q³ -   243q⁴     c(1) =  54
n= 4, e= 8 : 1 -  8q +  20q² +    0q³ -    62q⁴     c(1) =  20
n= 5, e= 6 : 1 -  6q +   9q² +   10q³ -    30q⁴     c(1) =   9
n= 7, e= 4 : 1 -  4q +   2q² +    8q³ -     5q⁴     c(1) =   2
n= 9, e= 3 : 1 -  3q +   0q² +    5q³ +     0q⁴     c(1) =   0
n=13, e= 2 : 1 -  2q -   1q² +    2q³ +     1q⁴     c(1) =  -1
n=25, e= 1 : 1 -  1q -   1q² +    0q³ +     0q⁴     c(1) =  -1
```

Predicted by the closed formula `a₁(a₁+3)/2 + a₂` with `a₁ = -e`, `a₂ = e` iff `n = 2`:
`276, 54, 20, 9, 2, 0, -1, -1`; total `359`.  The `q¹`-coefficient `-e` is the constant
term of `1/η_g`, which is why the normalized McKay–Thompson series is `1/η_g + e`.

A discarded hypothesis: `c(1) = a₂ - a₁` (predicts `12` for `n = 3`, true value `54`).
-/


open MoonshineHeadTable in
theorem solution(e : ℤ) : 0 ≤ headCoeff (pmFrame 2 e) := by
  rw [headCoeff_pmFrame_two]
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ e * (e - 3) := by
    rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (e - 3), by rw [ht]; ring⟩
    · exact ⟨e * (t - 1), by rw [ht]; ring⟩
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hfac : 0 ≤ (e - 1) * e := by
    rcases le_or_gt e 0 with h | h
    · nlinarith
    · nlinarith [show (1 : ℤ) ≤ e by omega]
  nlinarith [hk, hfac]
