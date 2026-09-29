-- Prove2me | Definitions.Def_Probability_EMLInformationGeometryDeepening
-- name    : Probability_EMLInformationGeometryDeepening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:19.662274+00:00
-- url     : https://prove2.me/theorems/3b2a7c32-9c8a-4b9e-a512-97d180baa7dd
-- title:
--   Aether Catalog definitions — Probability_EMLInformationGeometryDeepening
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.EMLInformationGeometryDeepening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/EMLInformationGeometryDeepening.lean by skeleton subtraction
import Mathlib

/-!
# Exact nullspace geometry for finite exp-log models

This file deepens the finite EML analysis from a single common exponential scale to
an arbitrary feature `g₁`.  It proves a general Gram/nullspace theorem for Fisher
matrices, applies it to the three-parameter exp-log model

`exp(θ₁ g₁(x)) * log(θ₂ g₂(x) + θ₃)`,

and isolates the precise obstruction caused by a constant exponential feature.
The result is stronger than merely exhibiting a zero determinant: every null
Fisher direction is characterized pointwise as a vanishing centered directional
score.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace EMLInformationGeometryDeepening

variable {ι : Type*} [Fintype ι]
variable {d : ℕ}

/-- Center a collection of score functions with respect to weights `p`. -/
def centeredScore (p : ι → ℝ) (s : ι → Fin d → ℝ) (i : ι) (j : Fin d) : ℝ :=
  s i j - ∑ k, p k * s k j

/-- The finite Fisher matrix is the weighted Gram matrix of centered scores. -/
def fisherMatrix (p : ι → ℝ) (s : ι → Fin d → ℝ) (j k : Fin d) : ℝ :=
  ∑ i, p i * centeredScore p s i j * centeredScore p s i k

/-- A tangent vector contracted with the centered score. -/
def directionalScore (p : ι → ℝ) (s : ι → Fin d → ℝ)
    (v : Fin d → ℝ) (i : ι) : ℝ :=
  ∑ j, v j * centeredScore p s i j




/-- Unnormalized weight of the three-parameter finite EML model. -/
def emlRaw (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ) (i : ι) : ℝ :=
  Real.exp (θ 0 * g₁ i) * Real.log (θ 1 * g₂ i + θ 2)

/-- Partition function of the EML model. -/
def emlMass (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ) : ℝ :=
  ∑ i, emlRaw g₁ g₂ θ i

/-- Normalized EML probability. -/
def emlProbability (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ) (i : ι) : ℝ :=
  emlRaw g₁ g₂ θ i / emlMass g₁ g₂ θ

/-- The three raw logarithmic parameter scores. -/
def emlRawScore (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ) (i : ι) : Fin 3 → ℝ
  | 0 => g₁ i
  | 1 => g₂ i / ((θ 1 * g₂ i + θ 2) * Real.log (θ 1 * g₂ i + θ 2))
  | 2 => 1 / ((θ 1 * g₂ i + θ 2) * Real.log (θ 1 * g₂ i + θ 2))





/-- The three-parameter EML Fisher matrix. -/
def emlFisher (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fisherMatrix (emlProbability g₁ g₂ θ) (emlRawScore g₁ g₂ θ)





end EMLInformationGeometryDeepening


