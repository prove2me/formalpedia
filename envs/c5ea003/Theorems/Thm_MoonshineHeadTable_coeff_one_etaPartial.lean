-- Prove2me | Theorems.Thm_MoonshineHeadTable_coeff_one_etaPartial
-- name    : MoonshineHeadTable.coeff_one_etaPartial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:29:55.560299+00:00
-- url     : https://prove2.me/theorems/b25680bf-d28d-4b16-9c01-680265e1e2d5
-- title:
--   Linear coefficient of the truncated eta quotient.
-- statement:
--   **Linear coefficient of the truncated eta quotient.**  It equals `a 1` as soon as
--   `M ≥ 1`; in particular it is independent of the truncation.
--
--   ```lean
--   theorem MoonshineHeadTable.coeff_one_etaPartial(a : ℕ → ℤ) {M : ℕ} (hM : 1 ≤ M) :
--       coeff 1 ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧) = ((a 1 : ℤ) : R) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/MoonshineHeadTable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/MoonshineHeadTable.lean#L296

-- Thm stub generated from NumberTheory/MoonshineHeadTable.lean
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

theorem MoonshineHeadTable.coeff_one_etaPartial(a : ℕ → ℤ) {M : ℕ} (hM : 1 ≤ M) :
    coeff 1 ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧) = ((a 1 : ℤ) : R) := by sorry
