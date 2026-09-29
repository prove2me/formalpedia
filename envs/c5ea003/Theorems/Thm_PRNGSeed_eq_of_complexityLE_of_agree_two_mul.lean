-- Prove2me | Theorems.Thm_PRNGSeed_eq_of_complexityLE_of_agree_two_mul
-- name    : PRNGSeed.eq_of_complexityLE_of_agree_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:47:01.329808+00:00
-- url     : https://prove2.me/theorems/ea254c70-4937-436d-9687-6412e9dac895
-- title:
--   `2L` samples determine the stream.
-- statement:
--   **`2L` samples determine the stream.**  Two streams of linear complexity at
--   most `L` that agree on the first `2L` symbols are equal.  This is the
--   correctness guarantee behind Berlekamp–Massey: after `2L` observations the
--   identification problem has at most one answer, so a seed-recovery pipeline may
--   commit.
--
--   ```lean
--   theorem PRNGSeed.eq_of_complexityLE_of_agree_two_mul{L : ℕ} {x y : ℕ → F}
--       (hx : ComplexityLE L x) (hy : ComplexityLE L y)
--       (hagree : ∀ i : ℕ, i < 2 * L → x i = y i) : x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGBerlekampMassey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGBerlekampMassey.lean#L235

-- Thm stub generated from MachineLearning/PRNGBerlekampMassey.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Why `2L` Samples Suffice: the Foundation of Berlekamp–Massey

`MachineLearning.PRNGSeedRecoveryLFSR` shows that a stream obeying a *known*
order-`L` recurrence is reproduced exactly from `L` symbols.  Detection is
harder: the taps are unknown, so different candidate registers compete.  This
file proves the theorem that makes fingerprinting possible at all:

> two streams of linear complexity at most `L` that agree on the first `2L`
> symbols agree **forever**.

Hence a `2L`-symbol observation window is enough to identify a stream inside the
complexity-`≤ L` class — the correctness guarantee behind Berlekamp–Massey, and
the reason a seed-recovery pipeline can commit after seeing `2L` samples.

## Method

The shift operator `shift : (ℕ → F) →ₗ[F] (ℕ → F)` turns `ℕ → F` into an
`F[X]`-module.  A stream is a solution of a recurrence exactly when the
recurrence's characteristic polynomial annihilates it (`isSolution_iff_aeval`).
Annihilators multiply, so the difference of two complexity-`≤ L` streams is
annihilated by a *monic degree-`2L`* polynomial, i.e. it is a solution of some
order-`2L` recurrence; vanishing on `2L` consecutive symbols then forces it to
vanish identically.

We reuse Mathlib's `LinearRecurrence` API (`charPoly`, `mkSol`,
`sol_eq_of_eq_init`) and bridge it to the `IsLinRec` predicate of the LFSR file.

## Main results

* `isSolution_iff_aeval` — solution ⟺ annihilated by the characteristic
  polynomial acting through the shift operator.
* `charPoly_recOfPoly` — every monic polynomial is the characteristic polynomial
  of an explicit linear recurrence.
* `complexityLE_add`, `complexityLE_sub` — linear complexity is subadditive.
* `eq_zero_of_complexityLE_of_init_zero` — a complexity-`m` stream vanishing on
  `m` initial symbols vanishes identically.
* `eq_of_complexityLE_of_agree_two_mul` — **`2L` samples determine the stream.**
* `complexity_detector_sound` — a detector that fits any order-`L` register to
  the first `2L` symbols has, in fact, fitted the entire stream.
* `distinct_lfsr_streams_differ_early` — two order-`L` registers with different
  output streams already differ inside the first `2L` symbols, so the
  observation window cannot be shortened below `2L` without ambiguity.

## Application keywords

Berlekamp–Massey, linear complexity, shift operator, characteristic polynomial,
PRNG fingerprinting, seed recovery, sample complexity
-/


open Finset Polynomial

open PRNGSeed

variable {F : Type*} [CommRing F]

/-! ### The shift operator and the `F[X]`-module structure on streams -/







/-! ### Recurrences from monic polynomials -/



/-! ### Linear complexity and the `2L` sample bound -/






variable [Nontrivial F]


variable [NoZeroDivisors F]

theorem PRNGSeed.eq_of_complexityLE_of_agree_two_mul{L : ℕ} {x y : ℕ → F}
    (hx : ComplexityLE L x) (hy : ComplexityLE L y)
    (hagree : ∀ i : ℕ, i < 2 * L → x i = y i) : x = y := by sorry
