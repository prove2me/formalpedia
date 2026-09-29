-- Prove2me | Theorems.Thm_RLHF_expPoly_eq_zero_of_zeros
-- name    : RLHF.expPoly_eq_zero_of_zeros
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:40:29.604902+00:00
-- url     : https://prove2.me/theorems/c5f84dc3-253c-4d73-8a9c-ef5d79d971be
-- title:
--   Exponential sums are a Chebyshev system.
-- statement:
--   **Exponential sums are a Chebyshev system.**  If the exponents `v₀ < ⋯ < v_{n-1}` are
--   distinct and the exponential polynomial `x ↦ ∑_j c_j e^{v_j x}` vanishes at `n` distinct
--   points, then every coefficient vanishes.  Proved by induction on `n`: dividing by `e^{v₀ x}`
--   and applying Rolle's theorem on each of the `n − 1` consecutive intervals produces `n − 1`
--   zeros of an exponential polynomial with `n − 1` exponents.
--
--   ```lean
--   theorem RLHF.expPoly_eq_zero_of_zeros:
--       ∀ (n : ℕ) (v c t : Fin n → ℝ), StrictMono v → StrictMono t →
--         (∀ i, ∑ j, c j * Real.exp (v j * t i) = 0) → ∀ j, c j = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFChebyshevSystem.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFChebyshevSystem.lean#L54

-- Thm stub generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling

/-!
# Exponential sums form a Chebyshev system: `n` arbitrary temperatures suffice

`RLHF.exp_sample_uniqueness` recovers the masses on `n` known reward levels from the
partition function at `n` *arithmetically spaced* inverse temperatures, by a Vandermonde
determinant.  This file removes the arithmetic-grid hypothesis: **any** `n` distinct
temperatures do.

The engine is the classical Descartes/Chebyshev fact, proved here by induction on the number
of exponents with Rolle's theorem supplying the inductive step:

* `RLHF.expPoly_eq_zero_of_zeros` — a real exponential polynomial `∑_{j<n} c_j e^{v_j x}`
  with `n` strictly increasing exponents that vanishes at `n` distinct points has all
  coefficients zero.  (Equivalently: a nonzero exponential polynomial with `n` exponents has
  at most `n − 1` real zeros.)
* `RLHF.exp_sample_uniqueness_general` — consequently two mass vectors on the same `n` known
  distinct levels are equal as soon as their exponential sums agree at `n` distinct
  temperatures.
* `RLHF.spectral_rigidity_sampled_general` — the RLHF audit statement: with `n` known
  candidate reward levels, `n` arbitrary distinct inverse temperatures determine the reward
  spectrum.

Combined with `RLHF.prony_three_samples_insufficient_spectra`, the picture for the sampling
question is complete in the known-level case, and provably different when the levels are
unknown.
-/

open RLHF

open Finset

theorem RLHF.expPoly_eq_zero_of_zeros:
    ∀ (n : ℕ) (v c t : Fin n → ℝ), StrictMono v → StrictMono t →
      (∀ i, ∑ j, c j * Real.exp (v j * t i) = 0) → ∀ j, c j = 0 := by sorry
