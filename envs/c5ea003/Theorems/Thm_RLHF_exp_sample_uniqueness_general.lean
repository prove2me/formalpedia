-- Prove2me | Theorems.Thm_RLHF_exp_sample_uniqueness_general
-- name    : RLHF.exp_sample_uniqueness_general
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:40:59.653581+00:00
-- url     : https://prove2.me/theorems/2ae44fa6-7f71-40de-af2f-a54233b2b78c
-- title:
--   Prony sampling at arbitrary temperatures.
-- statement:
--   **Prony sampling at arbitrary temperatures.**  Two mass vectors on the same `n` known
--   strictly increasing levels that give the same exponential sum at `n` distinct temperatures
--   are equal.  This removes the arithmetic-grid hypothesis of
--   `RLHF.exp_sample_uniqueness`.
--
--   ```lean
--   theorem RLHF.exp_sample_uniqueness_general{n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
--       {t : Fin n → ℝ} (ht : StrictMono t) {a b : Fin n → ℝ}
--       (h : ∀ i, ∑ j, a j * Real.exp (v j * t i) = ∑ j, b j * Real.exp (v j * t i)) :
--       a = b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFChebyshevSystem.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFChebyshevSystem.lean#L146

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

theorem RLHF.exp_sample_uniqueness_general{n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
    {t : Fin n → ℝ} (ht : StrictMono t) {a b : Fin n → ℝ}
    (h : ∀ i, ∑ j, a j * Real.exp (v j * t i) = ∑ j, b j * Real.exp (v j * t i)) :
    a = b := by sorry
