-- Prove2me | Theorems.Thm_RLHF_spectral_rigidity_sampled_general
-- name    : RLHF.spectral_rigidity_sampled_general
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:47:46.861768+00:00
-- url     : https://prove2.me/theorems/750728f4-a0c0-4cb8-9eed-cc82816c080f
-- title:
--   Finite-sample spectral rigidity at arbitrary temperatures.
-- statement:
--   **Finite-sample spectral rigidity at arbitrary temperatures.**  With `n` known candidate
--   reward levels, the reward spectrum of an RLHF problem is determined by the partition function
--   at any `n` distinct inverse temperatures.
--
--   ```lean
--   theorem RLHF.spectral_rigidity_sampled_general{Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
--       {r₁ p₁ : Ω₁ → ℝ} {r₂ p₂ : Ω₂ → ℝ} {n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
--       (h₁ : image r₁ univ ⊆ image v univ) (h₂ : image r₂ univ ⊆ image v univ)
--       {t : Fin n → ℝ} (ht : StrictMono t)
--       (h : ∀ i, ∑ y, p₁ y * Real.exp (r₁ y * t i) = ∑ y, p₂ y * Real.exp (r₂ y * t i)) :
--       ∀ w : ℝ, rewardMass r₁ p₁ w = rewardMass r₂ p₂ w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFChebyshevSystem.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFChebyshevSystem.lean#L166

-- Thm stub generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Definitions.Def_NumberTheory_RLHFSpectralRigidity

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

theorem RLHF.spectral_rigidity_sampled_general{Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    {r₁ p₁ : Ω₁ → ℝ} {r₂ p₂ : Ω₂ → ℝ} {n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
    (h₁ : image r₁ univ ⊆ image v univ) (h₂ : image r₂ univ ⊆ image v univ)
    {t : Fin n → ℝ} (ht : StrictMono t)
    (h : ∀ i, ∑ y, p₁ y * Real.exp (r₁ y * t i) = ∑ y, p₂ y * Real.exp (r₂ y * t i)) :
    ∀ w : ℝ, rewardMass r₁ p₁ w = rewardMass r₂ p₂ w := by sorry
