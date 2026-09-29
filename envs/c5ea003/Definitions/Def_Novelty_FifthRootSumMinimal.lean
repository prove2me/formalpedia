-- Prove2me | Definitions.Def_Novelty_FifthRootSumMinimal
-- name    : Novelty_FifthRootSumMinimal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:34.48207+00:00
-- url     : https://prove2.me/theorems/91f4b7ca-109a-43c1-92c5-72ebd6ada0a4
-- title:
--   Aether Catalog definitions — Novelty_FifthRootSumMinimal
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FifthRootSumMinimal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FifthRootSumMinimal.lean by skeleton subtraction
import Mathlib

/-!
# Minimal absolute value of sums of powers of the fifth root of unity

Let `ζ₅ = exp(2πi/5)` be the standard primitive fifth root of unity.  A *sum of `n`
powers of `ζ₅`* is any complex number of the form

  `∑_{j < n} ζ₅ ^ (c j)`

for some choice of exponents `c : ℕ → ℕ`.  We define `σ₅ n` to be the infimum of the
absolute values of all such sums:

  `σ₅ n = inf { ‖∑_{j < n} ζ₅ ^ (c j)‖ : c : ℕ → ℕ }`.

Because only the residues of the exponents modulo `5` matter (as `ζ₅ ^ 5 = 1`), the sum
is really a nonnegative-integer combination `∑_{r} a_r ζ₅ ^ r` with `∑_r a_r = n`, and
`σ₅ n` is the least absolute value of such a combination.

The fundamental structural fact used throughout is that the five roots sum to zero,
`∑_{i < 5} ζ₅ ^ i = 0`, which lets one insert a full "zero-summing block" of five roots
without changing the value of a sum — the engine behind the monotonicity results in
`Catalog.FINAL.Novelty.FifthRootSumMonotonicity`.

This file provides the definition `σ₅` (`sigma5`) together with the basic facts:

* `zeta5_primRoot`  : `ζ₅` is a primitive fifth root of unity;
* `zeta5_pow_five`  : `ζ₅ ^ 5 = 1`;
* `zeta5_geom_sum`  : `∑_{i < 5} ζ₅ ^ i = 0`;
* `zeta5_pow_mod`   : `ζ₅ ^ n = ζ₅ ^ (n % 5)` (the multiplicative order-5 reduction);
* `sigma5_nonneg`, `sigma5_bddBelow`, `sigma5_set_nonempty`.
-/

open scoped BigOperators

namespace FifthRootSumMinimal

/-- The standard primitive fifth root of unity `ζ₅ = exp(2πi/5)`. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 : ℕ))





/-- The set of absolute values of all sums of `n` powers of `ζ₅`. -/
noncomputable def sumAbsSet (n : ℕ) : Set ℝ :=
  Set.range (fun c : ℕ → ℕ => ‖∑ j ∈ Finset.range n, zeta5 ^ c j‖)

/-- `σ₅ n`: the (infimum of the) minimal absolute value of a sum of `n` powers of the
primitive fifth root of unity `ζ₅`. -/
noncomputable def sigma5 (n : ℕ) : ℝ := sInf (sumAbsSet n)





end FifthRootSumMinimal


