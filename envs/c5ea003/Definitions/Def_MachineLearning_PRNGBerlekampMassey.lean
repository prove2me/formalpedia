-- Prove2me | Definitions.Def_MachineLearning_PRNGBerlekampMassey
-- name    : MachineLearning_PRNGBerlekampMassey
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:50:16.012985+00:00
-- url     : https://prove2.me/theorems/ac2687d4-6238-4c74-adab-dcfcf3595fa1
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGBerlekampMassey
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGBerlekampMassey`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGBerlekampMassey.lean by skeleton subtraction
import Mathlib
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

namespace PRNGSeed

variable {F : Type*} [CommRing F]

/-! ### The shift operator and the `F[X]`-module structure on streams -/

/-- The left shift operator on streams. -/
def shift : (ℕ → F) →ₗ[F] (ℕ → F) where
  toFun x := fun n => x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl






/-! ### Recurrences from monic polynomials -/

/-- The linear recurrence of order `m` whose characteristic polynomial is a given
monic degree-`m` polynomial. -/
def recOfPoly (m : ℕ) (r : F[X]) : LinearRecurrence F where
  order := m
  coeffs := fun i => -r.coeff (i : ℕ)


/-! ### Linear complexity and the `2L` sample bound -/

/-- A stream has linear complexity at most `L` when some order-`L` register
generates it. -/
def ComplexityLE (L : ℕ) (x : ℕ → F) : Prop := ∃ c : Fin L → F, IsLinRec L c x




section Field

variable [Nontrivial F]


variable [NoZeroDivisors F]




end Field

/-! ### Bridge to Mathlib's `LinearRecurrence` -/

/-- The Mathlib linear recurrence attached to a tap vector. -/
def lfsrRec {L : ℕ} (c : Fin L → F) : LinearRecurrence F := ⟨L, c⟩



end PRNGSeed


