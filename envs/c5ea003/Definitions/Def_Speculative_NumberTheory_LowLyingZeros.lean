-- Prove2me | Definitions.Def_Speculative_NumberTheory_LowLyingZeros
-- name    : Speculative_NumberTheory_LowLyingZeros
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:02.665033+00:00
-- url     : https://prove2.me/theorems/ce7c87df-5fca-4940-b6c4-c02c85dddf38
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_LowLyingZeros
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.LowLyingZeros`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/LowLyingZeros.lean by skeleton subtraction
import Mathlib

/-!
# Explicit bounds on low-lying zeros of automorphic L-functions

This file formalizes, in an abstract but faithful form, the two analytic pillars that
underlie explicit results on the low-lying zeros of automorphic `L`-functions.

## The de la Vallée Poussin positivity

Every classical proof of a zero-free region for an `L`-function — and hence every
explicit statement that its low-lying zeros stay away from the line `ℜ(s) = 1`, pushing
them towards the critical line `ℜ(s) = 1/2` — rests on the elementary trigonometric
inequality
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`.
Applied to a Dirichlet series `log L(s) = ∑ b_n λ_n^{-s}` with **nonnegative** coefficients
(the situation for `ζ`, for `L`-functions of self-dual cuspidal representations, and for
symmetric-power `L`-functions on the edge of the critical strip), it gives the positivity
`3 · A(σ,0) + 4 · A(σ,t) + A(σ,2t) ≥ 0`, which forbids a zero on `ℜ(s)=1`.

We prove this positivity for an arbitrary finite nonnegative Dirichlet cosine sum
`dirichletCosSum` (`dirichletCosSum_three_four_one_nonneg`), together with the exact
trinomial identity (`three_four_one_cos`) and its sharp equality case
(`three_four_one_cos_eq_zero_iff`).

## Functional-equation symmetry about the critical line

The completed `L`-function of an automorphic representation satisfies a functional equation
of the shape `Λ(s) = ε · conj (Λ(1 - conj s))` with `|ε| = 1`.  The map
`s ↦ 1 - conj s` is precisely the reflection of the complex plane across the critical line
`ℜ(s) = 1/2`.  Consequently the zero set of `Λ` is symmetric under this reflection, its
fixed points are exactly the points on the critical line, and every zero off the critical
line occurs in a genuine mirror pair of two distinct zeros.

* `critical_reflection_involutive` — `s ↦ 1 - conj s` is an involution.
* `critical_reflection_fixed_iff` — its fixed points are exactly `{s : ℜ s = 1/2}`.
* `zero_reflect_iff` — `Λ s = 0 ↔ Λ (1 - conj s) = 0`.
* `offcritical_zero_pair` — an off-line zero forces a distinct mirror zero.

Together these give a rigorous, self-contained account of *why* the nontrivial zeros of an
automorphic `L`-function are symmetric about `ℜ(s)=1/2` and *why* the positivity method
keeps the low-lying ones off the edge of the critical strip.
-/

namespace LowLyingZeros

open Finset Real

/-! ## The de la Vallée Poussin trinomial -/




/-! ## Nonnegative Dirichlet cosine sums -/

/-- A finite Dirichlet-type cosine sum
`∑_{n ∈ F} a n · (r n)^(-σ) · cos (t · φ n)`.
Modelling `A(σ,t) = ℜ ∑ b_n λ_n^{-σ-it}` with `b_n = a n ≥ 0`, `λ_n = r n > 0`,
`φ n = log λ_n`, this is the real part of the logarithm of an `L`-function on a
vertical line, truncated to a finite spectrum. -/
noncomputable def dirichletCosSum {ι : Type*} (F : Finset ι) (a r φ : ι → ℝ)
    (σ t : ℝ) : ℝ :=
  ∑ n ∈ F, a n * r n ^ (-σ) * Real.cos (t * φ n)

variable {ι : Type*} (F : Finset ι) (a r φ : ι → ℝ)



/-! ## Functional-equation symmetry about the critical line -/

/-- The **critical reflection** `s ↦ 1 - conj s`, the reflection of `ℂ` across the
critical line `ℜ(s) = 1/2`. -/
def criticalReflection (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s







end LowLyingZeros


