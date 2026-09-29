-- Prove2me | Definitions.Def_Probability_FisherCramerRao
-- name    : Probability_FisherCramerRao
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:15.6812+00:00
-- url     : https://prove2.me/theorems/268cdc94-dc49-4e6a-9548-5098b9e5e683
-- title:
--   Aether Catalog definitions — Probability_FisherCramerRao
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.FisherCramerRao`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/FisherCramerRao.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.NeuralCoding.Fisher

open Finset

variable {X : Type*} [Fintype X]

/-- **Fisher information** of a response distribution `p` with stimulus
derivative `p'`: `I = ∑ x, p'(x)² / p(x)`. -/
noncomputable def fisherInfo (p p' : X → ℝ) : ℝ := ∑ x, (p' x) ^ 2 / p x

/-- Variance of a decoder `T` about the true stimulus `θ`. -/
def estVariance (p T : X → ℝ) (θ : ℝ) : ℝ := ∑ x, p x * (T x - θ) ^ 2

variable {p : ℝ → X → ℝ} {p' T : X → ℝ} {θ : ℝ}






/-! ## Sharpness: a two-response population attaining the bound -/

/-- A two-response population code: response `true` has probability `1/2 + θ`. -/
noncomputable def bernoulliCode : ℝ → Bool → ℝ := fun t b => if b then 1 / 2 + t else 1 / 2 - t

/-- Its stimulus derivative. -/
def bernoulliDeriv : Bool → ℝ := fun b => if b then 1 else -1

/-- The natural unbiased decoder. -/
noncomputable def bernoulliDecoder : Bool → ℝ := fun b => if b then 1 / 2 else -1 / 2






end Catalog.Probability.NeuralCoding.Fisher


