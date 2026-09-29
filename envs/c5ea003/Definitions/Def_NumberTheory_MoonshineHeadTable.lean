-- Prove2me | Definitions.Def_NumberTheory_MoonshineHeadTable
-- name    : NumberTheory_MoonshineHeadTable
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:47.33317+00:00
-- url     : https://prove2.me/theorems/2c94cea4-723b-4c87-97cf-0f2384651d37
-- title:
--   Aether Catalog definitions — NumberTheory_MoonshineHeadTable
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.MoonshineHeadTable`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/MoonshineHeadTable.lean by skeleton subtraction
import Mathlib

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

namespace MoonshineHeadTable

open PowerSeries Finset

/-! ## 1. Newton identities for low coefficients of products, over any ring -/

section Jets

variable {R : Type*} [CommRing R] {ι : Type*}





/-! ## 2. The `2`-jet of an integer power of a unit power series -/



end Jets

/-! ## 3. Truncated eta quotients attached to a frame shape -/

section Eta

variable (R : Type*) [CommRing R]

/-- The unit `1 - q^(m+1)` of `R⟦q⟧`. -/
noncomputable def oneSubXPowUnit (m : ℕ) : (R⟦X⟧)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr
    (by simp : IsUnit (constantCoeff ((1 : R⟦X⟧) - X ^ (m + 1))))).unit

variable {R}





/-- Divisor sum of a frame shape: `b m = ∑_{k ∣ m} a k`.  Collecting the factors of
`∏_k ∏_n (1 - q^{k n})^{-a k}` by the total degree `m = k n` turns it into
`∏_m (1 - q^m)^{-b m}`. -/
def divSum (a : ℕ → ℤ) (m : ℕ) : ℤ := ∑ k ∈ m.divisors, a k



variable (R) in
/-- The truncated eta quotient `∏_{m = 1}^{M} (1 - q^m) ^ (-b m)`, a unit of `R⟦q⟧`.
For a balanced frame shape this is `q · (1 / η_g)` truncated after the `M`-th
factor. -/
noncomputable def etaPartial (a : ℕ → ℤ) (M : ℕ) : (R⟦X⟧)ˣ :=
  ∏ m ∈ Finset.range M, (oneSubXPowUnit R m) ^ (-(divSum a (m + 1)))

/-- The `m`-th factor of the truncated eta quotient, as a power series. -/
noncomputable def etaFactor (a : ℕ → ℤ) (m : ℕ) : R⟦X⟧ :=
  (((oneSubXPowUnit R m) ^ (-(divSum a (m + 1))) : (R⟦X⟧)ˣ) : R⟦X⟧)









end Eta

/-! ## 4. The closed formula for the head coefficient -/

/-- The head coefficient `c_g(1)` predicted by a frame shape `∏ k ^ (a k)`:
`a 1 (a 1 + 3) / 2 + a 2`.  The division is exact, see `two_mul_headCoeff`. -/
def headCoeff (a : ℕ → ℤ) : ℤ := a 1 * (a 1 + 3) / 2 + a 2




/-! ## 5. The balanced frame shapes `1^(-e) n^(e)` and the derived head table -/

/-- The frame shape `1^(-e) n^(e)` (with `n ≠ 1`), i.e. `η_g = η(n τ)^e / η(τ)^e`.
It is *balanced*, `∑ k * a k = 24`, exactly when `e * (n - 1) = 24`. -/
def pmFrame (n : ℕ) (e : ℤ) : ℕ → ℤ :=
  fun k => if k = 1 then -e else if k = n then e else 0



/-- The eight balanced frame shapes `1^(-e) n^(e)` with `e * (n - 1) = 24`:
`n = 2, 3, 4, 5, 7, 9, 13, 25` with `e = 24, 12, 8, 6, 4, 3, 2, 1`.  These are
exactly the `n` with `n - 1 ∣ 24`. -/
def pmData : Fin 8 → ℕ × ℤ :=
  ![(2, 24), (3, 12), (4, 8), (5, 6), (7, 4), (9, 3), (13, 2), (25, 1)]


/-- The derived head table: `c_g(1)` for the eight eta-quotient frame shapes. -/
def etaHeadTable : Fin 8 → ℤ := fun i => headCoeff (pmFrame (pmData i).1 (pmData i).2)



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

end MoonshineHeadTable


