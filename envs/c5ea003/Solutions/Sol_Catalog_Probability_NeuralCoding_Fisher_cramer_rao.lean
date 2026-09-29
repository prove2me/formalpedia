-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Fisher.cramer_rao
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:57.542828+00:00
-- url     : https://prove2.me/submissions/cb25d3c0-a3dc-41c8-af04-708b8f1f4686

-- Sol generated from Probability/FisherCramerRao.lean
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

/-- **The scores have mean zero.**  Differentiating the normalisation identity
gives `∑ x, p' x = 0`. -/
theorem sum_deriv_eq_zero
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
    (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1) :
    ∑ x, p' x = 0 := by
  have hd1 : HasDerivAt (fun t => ∑ x, p t x) (∑ x, p' x) θ :=
    HasDerivAt.fun_sum (fun x _ => hderiv x)
  have heq : (fun t => ∑ x, p t x) =ᶠ[nhds θ] (fun _ => (1 : ℝ)) := hnorm
  have hd2 : HasDerivAt (fun t => ∑ x, p t x) 0 θ :=
    (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq heq
  exact hd1.unique hd2

/-- Differentiating local unbiasedness: `∑ x, T x * p' x = 1`. -/
theorem sum_mul_deriv_eq_one
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
    (hunb : ∀ᶠ t in nhds θ, ∑ x, T x * p t x = t) :
    ∑ x, T x * p' x = 1 := by
  have hd1 : HasDerivAt (fun t => ∑ x, T x * p t x) (∑ x, T x * p' x) θ :=
    HasDerivAt.fun_sum (fun x _ => (hderiv x).const_mul (T x))
  have heq : (fun t => ∑ x, T x * p t x) =ᶠ[nhds θ] (fun t => t) := hunb
  have hd2 : HasDerivAt (fun t => ∑ x, T x * p t x) 1 θ :=
    (hasDerivAt_id θ).congr_of_eventuallyEq heq
  exact hd1.unique hd2

/-- The centred decoder has unit correlation with the score. -/
theorem sum_centered_mul_deriv
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
    (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1)
    (hunb : ∀ᶠ t in nhds θ, ∑ x, T x * p t x = t) :
    ∑ x, (T x - θ) * p' x = 1 := by
  have h0 := sum_deriv_eq_zero hderiv hnorm
  have h1 := sum_mul_deriv_eq_one (T := T) hderiv hunb
  have hsplit : ∑ x, (T x - θ) * p' x = (∑ x, T x * p' x) - θ * ∑ x, p' x := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  rw [hsplit, h0, h1]
  ring



/-! ## Sharpness: a two-response population attaining the bound -/










open Catalog.Probability.NeuralCoding.Fisher in
theorem solution(hpos : ∀ x, 0 < p θ x)
    (hderiv : ∀ x, HasDerivAt (fun t => p t x) (p' x) θ)
    (hnorm : ∀ᶠ t in nhds θ, ∑ x, p t x = 1)
    (hunb : ∀ᶠ t in nhds θ, ∑ x, T x * p t x = t) :
    1 ≤ estVariance (p θ) T θ * fisherInfo (p θ) p' := by
  classical
  set f : X → ℝ := fun x => Real.sqrt (p θ x) * (T x - θ) with hf
  set g : X → ℝ := fun x => p' x / Real.sqrt (p θ x) with hg
  have hsqrt_pos : ∀ x, 0 < Real.sqrt (p θ x) := fun x => Real.sqrt_pos.mpr (hpos x)
  have hfg : ∀ x, f x * g x = (T x - θ) * p' x := by
    intro x
    have hne : Real.sqrt (p θ x) ≠ 0 := (hsqrt_pos x).ne'
    show Real.sqrt (p θ x) * (T x - θ) * (p' x / Real.sqrt (p θ x)) = (T x - θ) * p' x
    field_simp
  have hf2 : ∀ x, f x ^ 2 = p θ x * (T x - θ) ^ 2 := by
    intro x
    have : Real.sqrt (p θ x) ^ 2 = p θ x := Real.sq_sqrt (hpos x).le
    rw [hf]
    rw [mul_pow, this]
  have hg2 : ∀ x, g x ^ 2 = (p' x) ^ 2 / p θ x := by
    intro x
    have hs : Real.sqrt (p θ x) ^ 2 = p θ x := Real.sq_sqrt (hpos x).le
    rw [hg, div_pow, hs]
  have hcs : (∑ x, f x * g x) ^ 2 ≤ (∑ x, f x ^ 2) * (∑ x, g x ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ f g
  have hone : (∑ x, f x * g x) = 1 := by
    rw [Finset.sum_congr rfl (fun x _ => hfg x)]
    exact sum_centered_mul_deriv hderiv hnorm hunb
  rw [hone] at hcs
  rw [Finset.sum_congr rfl (fun x _ => hf2 x), Finset.sum_congr rfl (fun x _ => hg2 x)] at hcs
  simpa [estVariance, fisherInfo] using hcs
