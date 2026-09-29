-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Fisher_cramer_rao
-- name    : Catalog.Probability.NeuralCoding.Fisher.cramer_rao
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:59:52.11428+00:00
-- url     : https://prove2.me/theorems/e88ac647-1d4d-444d-946a-c67d27412b1a
-- title:
--   Cramér–Rao bound for a finite population code.
-- statement:
--   **Cramér–Rao bound for a finite population code.**  Every locally unbiased
--   decoder `T` of the stimulus `θ` satisfies `1 ≤ Var(T) * I(θ)`: the decoding
--   variance cannot beat the reciprocal Fisher information of the population.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Fisher.cramer_rao(hpos : ∀ x, 0 < p θ x)
--       (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
--       (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1)
--       (hunb : ∀ᶠ t in nhds θ, ∑ x, T x * p t x = t) :
--       1 ≤ estVariance (p θ) T θ * fisherInfo (p θ) p' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/FisherCramerRao.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/FisherCramerRao.lean#L88

-- Thm stub generated from Probability/FisherCramerRao.lean
import Mathlib
import Definitions.Def_Probability_FisherCramerRao
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fisher information and the Cramér–Rao bound for nonlinear population codes

The population-coding results of `Catalog/Novelty/NeuralCoding.lean` and of
`Catalog/Probability/NeuralCoding/IIDPopulationCoding.lean` bound the error of an
*averaging* estimator.  The fundamental limit for an arbitrary decoder of a
(possibly nonlinear) population code is instead the Cramér–Rao bound, proved
here for a finitely supported response distribution.

## Model

A population code is a family of response distributions `p θ : X → ℝ` on a
finite response set `X`, parametrised by the encoded stimulus `θ ∈ ℝ`.  A
decoder is a function `T : X → ℝ`, unbiased near `θ` if `∑ x, T x * p t x = t`
for all `t` near `θ`.

## Results

1. `sum_deriv_eq_zero` — the scores have mean zero.
2. `sum_centered_mul_deriv` — the centred decoder correlates with the score
   exactly to first order.
3. `cramer_rao` — **the Cramér–Rao bound**: `1 ≤ Var(T) * I(θ)` for every
   locally unbiased decoder, i.e. no decoder beats `1 / I(θ)`.
4. `variance_ge_inv_fisher` — the same statement as a variance lower bound.
5. `bernoulli_cramer_rao_sharp` — the bound is **sharp**: a two-response
   population with `I = 4` admits an unbiased decoder of variance exactly `1/4`.
-/

open Catalog.Probability.NeuralCoding.Fisher

open Finset

variable {X : Type*} [Fintype X]



variable {p : ℝ → X → ℝ} {p' T : X → ℝ} {θ : ℝ}

theorem Catalog.Probability.NeuralCoding.Fisher.cramer_rao(hpos : ∀ x, 0 < p θ x)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
    (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1)
    (hunb : ∀ᶠ t in nhds θ, ∑ x, T x * p t x = t) :
    1 ≤ estVariance (p θ) T θ * fisherInfo (p θ) p' := by sorry
