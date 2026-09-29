-- Prove2me | solution 1 for MoonshineHeadTable.two_mul_coeff_two_prod_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T19:03:15.318988+00:00
-- url     : https://prove2.me/submissions/21e92804-028a-4be0-a868-523eee4fe759

import Mathlib
import Definitions.Def_NumberTheory_MoonshineHeadTable

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/NumberTheory/MoonshineHeadTable.lean ====
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

/-- The quadratic coefficient of a product of two power series. -/
theorem coeff_two_mul (a b : R⟦X⟧) :
    coeff 2 (a * b) =
      constantCoeff a * coeff 2 b + coeff 1 a * coeff 1 b + coeff 2 a * constantCoeff b := by
  have hanti : Finset.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := rfl
  rw [PowerSeries.coeff_mul, hanti]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [coeff_zero_eq_constantCoeff]
  ring

/-- Constant coefficient of a finite product of power series with constant term `1`. -/
theorem constantCoeff_prod_one (s : Finset ι) (g : ι → R⟦X⟧)
    (h : ∀ i ∈ s, constantCoeff (g i) = 1) : constantCoeff (∏ i ∈ s, g i) = 1 := by
  rw [map_prod, Finset.prod_congr rfl h, Finset.prod_const_one]

/-- **Newton identity, level 1.** The linear coefficient of a finite product of power
series with constant term `1` is the sum of the linear coefficients. -/
theorem coeff_one_prod_one (s : Finset ι) (g : ι → R⟦X⟧)
    (h : ∀ i ∈ s, constantCoeff (g i) = 1) :
    coeff 1 (∏ i ∈ s, g i) = ∑ i ∈ s, coeff 1 (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hsub : ∀ i ∈ s, constantCoeff (g i) = 1 :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, PowerSeries.coeff_one_mul, constantCoeff_prod_one s g hsub,
        h a (Finset.mem_insert_self a s), ih hsub, Finset.sum_insert ha]
      ring

/-- **Newton identity, level 2.** For power series with constant term `1`, twice the
quadratic coefficient of a finite product is twice the sum of the quadratic
coefficients plus the second elementary symmetric function of the linear
coefficients, written without division as `(∑ c)² - ∑ c²`. -/
theorem two_mul_coeff_two_prod_one (s : Finset ι) (g : ι → R⟦X⟧)
    (h : ∀ i ∈ s, constantCoeff (g i) = 1) :
    2 * coeff 2 (∏ i ∈ s, g i) =
      2 * (∑ i ∈ s, coeff 2 (g i)) + (∑ i ∈ s, coeff 1 (g i)) ^ 2
        - ∑ i ∈ s, (coeff 1 (g i)) ^ 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hsub : ∀ i ∈ s, constantCoeff (g i) = 1 :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ihs := ih hsub
      rw [Finset.prod_insert ha, coeff_two_mul, constantCoeff_prod_one s g hsub,
        coeff_one_prod_one s g hsub, h a (Finset.mem_insert_self a s),
        Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      linear_combination ihs

/-! ## 2. The `2`-jet of an integer power of a unit power series -/

/-- The constant coefficient of the inverse of a unit with constant coefficient `1`. -/
theorem constantCoeff_inv_units (u : (R⟦X⟧)ˣ) (hu : constantCoeff (u : R⟦X⟧) = 1) :
    constantCoeff ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
  have h : (u : R⟦X⟧) * ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have := congrArg (constantCoeff (R := R)) h
  rw [map_mul, hu, one_mul, map_one] at this
  exact this

/-- **The `2`-jet of `u ^ z`.** For a unit power series `u = 1 + c₁ q + c₂ q² + ⋯` and
any integer exponent `z`, the constant, linear and quadratic coefficients of `u ^ z`
are given by the binomial formulas `1`, `z c₁`, and `z c₂ + z(z-1)/2 · c₁²`
(the last written multiplied by `2` to stay in the ring). -/
theorem jet_zpow (u : (R⟦X⟧)ˣ) (hu : constantCoeff (u : R⟦X⟧) = 1) (z : ℤ) :
    constantCoeff (((u ^ z : (R⟦X⟧)ˣ)) : R⟦X⟧) = 1 ∧
      coeff 1 (((u ^ z : (R⟦X⟧)ˣ)) : R⟦X⟧) = (z : R) * coeff 1 (u : R⟦X⟧) ∧
      2 * coeff 2 (((u ^ z : (R⟦X⟧)ˣ)) : R⟦X⟧) =
        2 * (z : R) * coeff 2 (u : R⟦X⟧)
          + (z : R) * ((z : R) - 1) * (coeff 1 (u : R⟦X⟧)) ^ 2 := by
  have hinv := constantCoeff_inv_units u hu
  -- coefficients of the inverse
  have hmul : (u : R⟦X⟧) * ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hi1 : coeff 1 ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) = - coeff 1 (u : R⟦X⟧) := by
    have := congrArg (coeff (R := R) 1) hmul
    rw [PowerSeries.coeff_one_mul, hu, hinv] at this
    simp only [mul_one, PowerSeries.coeff_one] at this
    norm_num at this
    linear_combination this
  have hi2 : coeff 2 ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧)
      = - coeff 2 (u : R⟦X⟧) + (coeff 1 (u : R⟦X⟧)) ^ 2 := by
    have := congrArg (coeff (R := R) 2) hmul
    rw [coeff_two_mul, hu, hinv, hi1] at this
    simp only [mul_one, one_mul, PowerSeries.coeff_one] at this
    norm_num at this
    linear_combination this
  induction z using Int.induction_on with
  | zero => simp
  | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hpow : ((u ^ ((n : ℤ) + 1) : (R⟦X⟧)ˣ) : R⟦X⟧)
          = ((u ^ (n : ℤ) : (R⟦X⟧)ˣ) : R⟦X⟧) * (u : R⟦X⟧) := by
        rw [zpow_add_one, Units.val_mul]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpow, map_mul, h0, hu, one_mul]
      · rw [hpow, PowerSeries.coeff_one_mul, h0, hu, h1]
        push_cast
        ring
      · rw [hpow, coeff_two_mul, h0, hu, h1]
        push_cast at h2 ⊢
        linear_combination h2
  | pred n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hpow : ((u ^ (-(n : ℤ) - 1) : (R⟦X⟧)ˣ) : R⟦X⟧)
          = ((u ^ (-(n : ℤ)) : (R⟦X⟧)ˣ) : R⟦X⟧) * ((u⁻¹ : (R⟦X⟧)ˣ) : R⟦X⟧) := by
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul]
      refine ⟨?_, ?_, ?_⟩
      · rw [hpow, map_mul, h0, hinv, one_mul]
      · rw [hpow, PowerSeries.coeff_one_mul, h0, hinv, h1, hi1]
        push_cast
        ring
      · rw [hpow, coeff_two_mul, h0, hinv, h1, hi1, hi2]
        push_cast at h2 ⊢
        linear_combination h2

end Jets

/-! ## 3. Truncated eta quotients attached to a frame shape -/

section Eta

variable (R : Type*) [CommRing R]

-- [dropped: platform already declares oneSubXPowUnit]
variable {R}

@[simp] theorem val_oneSubXPowUnit (m : ℕ) :
    ((oneSubXPowUnit R m : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 - X ^ (m + 1) :=
  IsUnit.unit_spec _

@[simp] theorem constantCoeff_oneSubXPowUnit (m : ℕ) :
    constantCoeff ((oneSubXPowUnit R m : (R⟦X⟧)ˣ) : R⟦X⟧) = 1 := by
  simp

theorem coeff_one_oneSubXPowUnit (m : ℕ) :
    coeff 1 ((oneSubXPowUnit R m : (R⟦X⟧)ˣ) : R⟦X⟧) = if m = 0 then -1 else 0 := by
  rw [val_oneSubXPowUnit]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  · rw [if_neg (by omega)]
    simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    rw [if_neg (by omega : ¬(1 : ℕ) = 0), if_neg (by omega : ¬(1 : ℕ) = m + 1)]
    ring

theorem coeff_two_oneSubXPowUnit (m : ℕ) :
    coeff 2 ((oneSubXPowUnit R m : (R⟦X⟧)ˣ) : R⟦X⟧) = if m = 1 then -1 else 0 := by
  rw [val_oneSubXPowUnit]
  by_cases hm : m = 1
  · subst hm; norm_num
  · rw [if_neg hm]
    simp only [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
    rw [if_neg (by omega : ¬(2 : ℕ) = 0), if_neg (by omega : ¬(2 : ℕ) = m + 1)]
    ring

/-- Divisor sum of a frame shape: `b m = ∑_{k ∣ m} a k`.  Collecting the factors of
`∏_k ∏_n (1 - q^{k n})^{-a k}` by the total degree `m = k n` turns it into
`∏_m (1 - q^m)^{-b m}`. -/
-- [dropped: platform already declares divSum]
@[simp] theorem divSum_one (a : ℕ → ℤ) : divSum a 1 = a 1 := by
  simp [divSum]

theorem divSum_two (a : ℕ → ℤ) : divSum a 2 = a 1 + a 2 := by
  have h : (2 : ℕ).divisors = {1, 2} := by decide
  simp [divSum, h]

variable (R) in
-- [dropped: platform already declares etaPartial]
-- [dropped: platform already declares etaFactor]
theorem val_etaPartial (a : ℕ → ℤ) (M : ℕ) :
    ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧) = ∏ m ∈ Finset.range M, etaFactor (R := R) a m := by
  rw [etaPartial, Units.coe_prod]
  rfl

theorem constantCoeff_etaFactor (a : ℕ → ℤ) (m : ℕ) :
    constantCoeff (etaFactor (R := R) a m) = 1 :=
  (jet_zpow (oneSubXPowUnit R m) (constantCoeff_oneSubXPowUnit m) _).1

theorem coeff_one_etaFactor (a : ℕ → ℤ) (m : ℕ) :
    coeff 1 (etaFactor (R := R) a m) = if m = 0 then ((divSum a 1 : ℤ) : R) else 0 := by
  have h := (jet_zpow (oneSubXPowUnit R m) (constantCoeff_oneSubXPowUnit m)
    (-(divSum a (m + 1)))).2.1
  rw [etaFactor, h, coeff_one_oneSubXPowUnit]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega)]; ring

theorem two_mul_coeff_two_etaFactor (a : ℕ → ℤ) (m : ℕ) :
    2 * coeff 2 (etaFactor (R := R) a m) =
      (if m = 0 then ((divSum a 1 * (divSum a 1 + 1) : ℤ) : R) else 0)
        + (if m = 1 then ((2 * divSum a 2 : ℤ) : R) else 0) := by
  have h := (jet_zpow (oneSubXPowUnit R m) (constantCoeff_oneSubXPowUnit m)
    (-(divSum a (m + 1)))).2.2
  rw [etaFactor, h, coeff_one_oneSubXPowUnit, coeff_two_oneSubXPowUnit]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [if_neg (by omega : ¬(0 : ℕ) = 1)]
    push_cast
    ring
  · rcases eq_or_ne m 1 with rfl | hm1
    · simp only [if_neg (by omega : ¬(1 : ℕ) = 0)]
      push_cast
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hm1]
      ring

/-- A sum over `range M` of a function supported in `{0, 1}` collapses. -/
theorem sum_range_of_support_le_two {M : ℕ} (hM : 2 ≤ M) (f : ℕ → R)
    (hf : ∀ m, 2 ≤ m → f m = 0) : ∑ m ∈ Finset.range M, f m = f 0 + f 1 := by
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> (simp only [Finset.mem_range]; omega)
  rw [← Finset.sum_subset hsub (fun x _ hx => hf x (by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx; omega))]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **Linear coefficient of the truncated eta quotient.**  It equals `a 1` as soon as
`M ≥ 1`; in particular it is independent of the truncation. -/
theorem coeff_one_etaPartial (a : ℕ → ℤ) {M : ℕ} (hM : 1 ≤ M) :
    coeff 1 ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧) = ((a 1 : ℤ) : R) := by
  rw [val_etaPartial]
  rw [coeff_one_prod_one _ _ (fun m _ => constantCoeff_etaFactor (R := R) a m)]
  have hsub : ({0} : Finset ℕ) ⊆ Finset.range M := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx; simp only [Finset.mem_range]; omega
  rw [← Finset.sum_subset hsub (fun x _ hx => by
    simp only [Finset.mem_singleton] at hx
    rw [coeff_one_etaFactor, if_neg hx])]
  rw [Finset.sum_singleton]
  simp [coeff_one_etaFactor, divSum_one]

/-- **Quadratic coefficient of the truncated eta quotient.**  For `M ≥ 2` it equals
`a 1 (a 1 + 1) / 2 + a 1 + a 2`, again independent of the truncation. -/
theorem two_mul_coeff_two_etaPartial (a : ℕ → ℤ) {M : ℕ} (hM : 2 ≤ M) :
    2 * coeff 2 ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧)
      = ((a 1 * (a 1 + 1) + 2 * (a 1 + a 2) : ℤ) : R) := by
  rw [val_etaPartial]
  rw [two_mul_coeff_two_prod_one _ _ (fun m _ => constantCoeff_etaFactor (R := R) a m)]
  have e1 : ∑ m ∈ Finset.range M, coeff 1 (etaFactor (R := R) a m) = ((a 1 : ℤ) : R) := by
    rw [sum_range_of_support_le_two hM _ (fun m hm => by
      rw [coeff_one_etaFactor, if_neg (by omega)])]
    rw [coeff_one_etaFactor, coeff_one_etaFactor, if_pos rfl, if_neg (by omega), divSum_one,
      add_zero]
  have e1sq : ∑ m ∈ Finset.range M, (coeff 1 (etaFactor (R := R) a m)) ^ 2
      = ((a 1 ^ 2 : ℤ) : R) := by
    rw [sum_range_of_support_le_two hM _ (fun m hm => by
      rw [coeff_one_etaFactor, if_neg (by omega)]; ring)]
    rw [coeff_one_etaFactor, coeff_one_etaFactor, if_pos rfl, if_neg (by omega), divSum_one]
    push_cast
    ring
  have e2 : 2 * ∑ m ∈ Finset.range M, coeff 2 (etaFactor (R := R) a m)
      = ((a 1 * (a 1 + 1) + 2 * (a 1 + a 2) : ℤ) : R) := by
    rw [Finset.mul_sum]
    rw [sum_range_of_support_le_two hM _ (fun m hm => by
      have := two_mul_coeff_two_etaFactor (R := R) a m
      rw [if_neg (by omega), if_neg (by omega)] at this
      simpa using this)]
    have h0 := two_mul_coeff_two_etaFactor (R := R) a 0
    have h1 := two_mul_coeff_two_etaFactor (R := R) a 1
    rw [if_pos rfl, if_neg (by omega)] at h0
    rw [if_neg (by omega), if_pos rfl] at h1
    rw [h0, h1, divSum_one, divSum_two]
    push_cast
    ring
  rw [e1, e1sq, e2]
  push_cast
  ring

/-- **Stability in the truncation.**  The quadratic coefficient of the truncated eta
quotient does not depend on `M` once `M ≥ 2`; hence it is a genuine coefficient of
the infinite product `∏_{m ≥ 1} (1 - q^m)^{-b m}`. -/
theorem coeff_two_etaPartial_stable (a : ℕ → ℤ) {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N) :
    (2 : R) * coeff 2 ((etaPartial R a M : (R⟦X⟧)ˣ) : R⟦X⟧)
      = 2 * coeff 2 ((etaPartial R a N : (R⟦X⟧)ˣ) : R⟦X⟧) := by
  rw [two_mul_coeff_two_etaPartial a hM, two_mul_coeff_two_etaPartial a hN]

end Eta

/-! ## 4. The closed formula for the head coefficient -/

-- [dropped: platform already declares headCoeff]
theorem even_mul_add_three (n : ℤ) : (2 : ℤ) ∣ n * (n + 3) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨k * (n + 3), by rw [hk]; ring⟩
  · exact ⟨n * (k + 2), by rw [hk]; ring⟩

theorem two_mul_headCoeff (a : ℕ → ℤ) :
    2 * headCoeff a = a 1 * (a 1 + 1) + 2 * (a 1 + a 2) := by
  obtain ⟨k, hk⟩ := even_mul_add_three (a 1)
  rw [headCoeff, hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  linarith [hk]

/-- **Main theorem: the head coefficient of an eta quotient is a frame-shape
polynomial.**  The coefficient of `q²` in `∏_{m = 1}^{M} (1 - q^m)^{-∑_{k ∣ m} a k}`
— equivalently the coefficient of `q¹` in the normalized series
`q⁻¹ ∏_{m ≥ 1} (1 - q^m)^{-∑_{k ∣ m} a k}` — equals `headCoeff a`, for every
truncation `M ≥ 2`. -/
theorem coeff_two_etaPartial (a : ℕ → ℤ) {M : ℕ} (hM : 2 ≤ M) :
    coeff 2 ((etaPartial ℤ a M : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧) = headCoeff a := by
  have h := two_mul_coeff_two_etaPartial (R := ℤ) a hM
  rw [Int.cast_id] at h
  have h2 := two_mul_headCoeff a
  linarith

/-! ## 5. The balanced frame shapes `1^(-e) n^(e)` and the derived head table -/

/-- The frame shape `1^(-e) n^(e)` (with `n ≠ 1`), i.e. `η_g = η(n τ)^e / η(τ)^e`.
It is *balanced*, `∑ k * a k = 24`, exactly when `e * (n - 1) = 24`. -/
-- [dropped: platform already declares pmFrame]
theorem headCoeff_pmFrame {n : ℕ} (hn : 2 < n) (e : ℤ) :
    headCoeff (pmFrame n e) = e * (e - 3) / 2 := by
  have h1 : pmFrame n e 1 = -e := by simp [pmFrame]
  have h2 : pmFrame n e 2 = 0 := by
    simp [pmFrame, show (2 : ℕ) ≠ 1 by norm_num, show (2 : ℕ) ≠ n by omega]
  rw [headCoeff, h1, h2, add_zero, show -e * (-e + 3) = e * (e - 3) by ring]

theorem headCoeff_pmFrame_two (e : ℤ) : headCoeff (pmFrame 2 e) = e * (e - 3) / 2 + e := by
  have h1 : pmFrame 2 e 1 = -e := by simp [pmFrame]
  have h2 : pmFrame 2 e 2 = e := by simp [pmFrame]
  rw [headCoeff, h1, h2, show -e * (-e + 3) = e * (e - 3) by ring]

/-- The eight balanced frame shapes `1^(-e) n^(e)` with `e * (n - 1) = 24`:
`n = 2, 3, 4, 5, 7, 9, 13, 25` with `e = 24, 12, 8, 6, 4, 3, 2, 1`.  These are
exactly the `n` with `n - 1 ∣ 24`. -/
-- [dropped: platform already declares pmData]
theorem pmData_balanced (i : Fin 8) :
    (pmData i).2 * (((pmData i).1 : ℤ) - 1) = 24 := by
  fin_cases i <;> decide

/-- The derived head table: `c_g(1)` for the eight eta-quotient frame shapes. -/
-- [dropped: platform already declares etaHeadTable]
theorem etaHeadTable_values :
    etaHeadTable = ![276, 54, 20, 9, 2, 0, -1, -1] := by
  funext i
  fin_cases i <;> (simp only [etaHeadTable, pmData, headCoeff, pmFrame]; decide)

/-- The sum of the eight derived head coefficients is `359`. -/
theorem sum_etaHeadTable : ∑ i, etaHeadTable i = 359 := by
  rw [etaHeadTable_values]
  decide

/-! ## 6. A structural constraint on the derived head coefficients

The closed formula lets us prove a *uniform* lower bound for the whole family of
balanced frame shapes `1^(-e) n^(e)`, with no case analysis on the eight admissible
pairs: the head coefficient is never smaller than `-1`.  The bound is attained
(at `e = 1` and `e = 2`, i.e. `n = 25` and `n = 13`), so it is sharp.  This is a
small, provable shadow of the positivity phenomena of Monstrous Moonshine. -/

theorem headCoeff_pmFrame_ge_neg_one {n : ℕ} (hn : 2 < n) (e : ℤ) :
    -1 ≤ headCoeff (pmFrame n e) := by
  rw [headCoeff_pmFrame hn]
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ e * (e - 3) := by
    rcases Int.even_or_odd e with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (e - 3), by rw [ht]; ring⟩
    · exact ⟨e * (t - 1), by rw [ht]; ring⟩
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hfac : 0 ≤ (e - 1) * (e - 2) := by
    rcases le_or_gt e 1 with h | h
    · nlinarith
    · nlinarith [show (2 : ℤ) ≤ e by omega]
  nlinarith [hk, hfac]

theorem headCoeff_pmFrame_two_nonneg (e : ℤ) : 0 ≤ headCoeff (pmFrame 2 e) := by
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

/-- The derived eight-entry table obeys the general bound, and attains it. -/
theorem etaHeadTable_ge_neg_one (i : Fin 8) : -1 ≤ etaHeadTable i := by
  rw [etaHeadTable_values]
  fin_cases i <;> decide

/-- The eight derived head coefficients are strictly decreasing in `n` except for the
final repetition `-1, -1`; in particular the table is antitone. -/
theorem etaHeadTable_antitone {i j : Fin 8} (hij : i ≤ j) : etaHeadTable j ≤ etaHeadTable i := by
  rw [etaHeadTable_values]
  fin_cases i <;> fin_cases j <;> simp_all

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
section
open MoonshineHeadTable
open PowerSeries Finset
variable {R : Type*} [CommRing R] {ι : Type*}

theorem solution (s : Finset ι) (g : ι → R⟦X⟧)
    (h : ∀ i ∈ s, constantCoeff (g i) = 1) :
    2 * coeff 2 (∏ i ∈ s, g i) =
      2 * (∑ i ∈ s, coeff 2 (g i)) + (∑ i ∈ s, coeff 1 (g i)) ^ 2
        - ∑ i ∈ s, (coeff 1 (g i)) ^ 2 := by
  first
  | exact MoonshineHeadTable.two_mul_coeff_two_prod_one s g h
  | exact MoonshineHeadTable.two_mul_coeff_two_prod_one
  | exact @MoonshineHeadTable.two_mul_coeff_two_prod_one s g h
  | apply MoonshineHeadTable.two_mul_coeff_two_prod_one
  | exact MoonshineHeadTable.two_mul_coeff_two_prod_one ..


end
