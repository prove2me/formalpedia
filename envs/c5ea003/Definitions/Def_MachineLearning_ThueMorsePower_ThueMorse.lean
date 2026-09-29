-- Prove2me | Definitions.Def_MachineLearning_ThueMorsePower_ThueMorse
-- name    : MachineLearning_ThueMorsePower_ThueMorse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:59:57.863743+00:00
-- url     : https://prove2.me/theorems/89feea5a-c8a9-4740-9825-e850f2634c24
-- title:
--   Aether Catalog definitions — MachineLearning_ThueMorsePower_ThueMorse
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.ThueMorsePower.ThueMorse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/ThueMorsePower/ThueMorse.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Thue–Morse generating function and its coefficient sequence

Let `T(x) = ∏_{k≥0} (1 - x^{2^k})`.  Expanding the product, the coefficient of
`x^n` is `(-1)^{s₂(n)}`, where `s₂(n)` is the number of `1`s in the binary
expansion of `n` (equivalently, the digit sum in base `2`); this is because the
binary representation of `n` is the *unique* way to write `n` as a sum of
distinct powers of two, and each factor `(1 - x^{2^k})` contributes a sign
`-1` when its term is selected.

We call this the **Thue–Morse sign sequence** `tm n = (-1)^{s₂(n)}`.

This file establishes the two defining functional recurrences of `tm` (which are
the coefficient-level form of the functional equation `T(x) = (1 - x)·T(x²)`),
together with the fact that every value is `±1`.  The latter is exactly the
statement that the `2`-adic valuation of the coefficients of `T(x)^1` is `0`
everywhere — the trivial (`m = 1`) case of the exact-valuation program pursued
in `Power5.lean`.

## Main results

* `tm_two_mul`         : `tm (2*n) = tm n`
* `tm_two_mul_add_one` : `tm (2*n+1) = - tm n`     (sign flip)
* `tm_eq_one_or_neg_one`, `tm_sq` : every value is `±1`
* `tm_not_two_dvd`     : `¬ 2 ∣ tm n`               (the `m = 1` valuation: `ν₂ = 0`)

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The coefficients of `T(x) = ∏(1-x^{2^k})` are the
  Thue–Morse signs `(-1)^{s₂(n)}`, and they satisfy `T(x) = (1-x) T(x²)`, whose
  coefficient form is `tm(2n)=tm n`, `tm(2n+1) = -tm n`.
Experiment (Experimenter): Verified computationally that
  `[tm 0,…,tm 15] = [1,-1,-1,1,-1,1,1,-1,-1,1,1,-1,1,-1,-1,1]`, matching the
  expansion of `∏_{k}(1-x^{2^k})` up to degree 15, and confirming both
  recurrences on `0 ≤ n ≤ 4000`.
Analysis (Analyst): The recurrences follow from `Nat.digits_def'`: appending the
  last binary digit `n % 2` either adds `0` (even) or `1` (odd) to the digit sum.
Critique (Critic): `tm` is genuinely `±1`-valued, so `¬ 2 ∣ tm n`; this is the
  base (`m=1`) case of the valuation program and is not vacuous.
-- !-- Lab Notes -- !--
-/


namespace ThueMorsePower

open scoped BigOperators

/-- The Thue–Morse sign sequence: the coefficient of `x^n` in
`T(x) = ∏_{k≥0} (1 - x^{2^k})`, equal to `(-1)^{s₂(n)}`. -/
def tm (n : ℕ) : ℤ := (-1) ^ ((Nat.digits 2 n).sum)







end ThueMorsePower


