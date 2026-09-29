-- Prove2me | Theorems.Thm_FifthRootSumMinimal_sigma5_set_nonempty
-- name    : FifthRootSumMinimal.sigma5_set_nonempty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:04.47451+00:00
-- url     : https://prove2.me/theorems/518a8ca2-5e09-475b-a6d8-d27e723ca64b
-- title:
--   `sumAbsSet n` is nonempty (take all exponents `0`).
-- statement:
--   `sumAbsSet n` is nonempty (take all exponents `0`).
--
--   ```lean
--   theorem FifthRootSumMinimal.sigma5_set_nonempty(n : ℕ) : (sumAbsSet n).Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FifthRootSumMinimal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FifthRootSumMinimal.lean#L74

-- Thm stub generated from Novelty/FifthRootSumMinimal.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootSumMinimal

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

open FifthRootSumMinimal

theorem FifthRootSumMinimal.sigma5_set_nonempty(n : ℕ) : (sumAbsSet n).Nonempty := by sorry
