-- Prove2me | Theorems.Thm_FifthRootSumMinimal_sigma5_step
-- name    : FifthRootSumMinimal.sigma5_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:19.406526+00:00
-- url     : https://prove2.me/theorems/32359d03-7610-4a4a-ae02-e9d83e1dff4c
-- title:
--   One-step monotonicity.
-- statement:
--   **One-step monotonicity.**  Appending a full zero-summing block of five roots does
--   not change the value of a sum, so any absolute value attainable with `n` powers of `ζ₅`
--   is attainable with `n + 5` powers; hence `σ₅ (n + 5) ≤ σ₅ n`.
--
--   ```lean
--   theorem FifthRootSumMinimal.sigma5_step(n : ℕ) : sigma5 (n + 5) ≤ sigma5 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FifthRootSumMonotonicity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FifthRootSumMonotonicity.lean#L40

-- Thm stub generated from Novelty/FifthRootSumMonotonicity.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootSumMinimal

/-!
# Monotonicity of `σ₅` along residue classes modulo 5

Using the definition of `σ₅` (`FifthRootSumMinimal.sigma5`) — the minimal absolute value
of a sum of `n` powers of the primitive fifth root of unity `ζ₅` — we prove the
conjecture that for each residue `r ∈ {0,1,2,3,4}` the sequence

  `k ↦ σ₅ (5 k + r)`

is non-increasing.

## The idea

The five roots satisfy `∑_{i < 5} ζ₅ ^ i = 0` (`FifthRootSumMinimal.zeta5_geom_sum`).
Hence, given any sum `S = ∑_{j < n} ζ₅ ^ (c j)` of `n` powers, we may append the five
exponents `0,1,2,3,4` to obtain a sum of `n + 5` powers with *the same value* `S`.
Therefore every absolute value attainable with `n` powers is also attainable with
`n + 5` powers, i.e. `sumAbsSet n ⊆ sumAbsSet (n + 5)`, and taking infima gives the
one-step inequality `σ₅ (n + 5) ≤ σ₅ n` (`sigma5_step`).

Specialising `n = 5 k + r` and noting `5 (k + 1) + r = (5 k + r) + 5` yields the
residue-wise monotonicity.

## No circular reasoning

`σ₅` is defined once and for all in `FifthRootSumMinimal`; the argument here only uses
the geometric-sum identity for `ζ₅` and elementary properties of infima of sets of
reals, so it is free of self-reference.  Exponent bookkeeping modulo `5` is governed by
the multiplicative order-`5` reduction `zeta5_pow_mod`, the fifth-root analogue of the
Fermat-little-theorem congruence recorded in
`Catalog.FINAL.Probability.FermatLittleFive`.
-/

open scoped BigOperators

open FifthRootSumMinimal

theorem FifthRootSumMinimal.sigma5_step(n : ℕ) : sigma5 (n + 5) ≤ sigma5 n := by sorry
