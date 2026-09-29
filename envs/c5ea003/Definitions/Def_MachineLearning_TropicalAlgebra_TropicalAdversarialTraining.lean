-- Prove2me | Definitions.Def_MachineLearning_TropicalAlgebra_TropicalAdversarialTraining
-- name    : MachineLearning_TropicalAlgebra_TropicalAdversarialTraining
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:37:25.765679+00:00
-- url     : https://prove2.me/theorems/70d9adc7-c5f8-445c-985b-19bdbd95febe
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalAlgebra_TropicalAdversarialTraining
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalAlgebra.TropicalAdversarialTraining`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalAlgebra/TropicalAdversarialTraining.lean by skeleton subtraction
import Mathlib

/-!
# Adversarial Training as Tropical Regularization

This file proves that adversarial robust training with hinge loss decomposes exactly
into empirical risk minimization plus a tropical (min-plus) penalty.

## Main Results

* `hingeLoss_shift_eq` — algebraic core: `hingeLoss(m - δ) = hingeLoss(m) + max(0, δ - marginSurplus(m))`
* `adversarial_eq_tropical` — **Theorem A**: shifted risk = empirical risk + tropical penalty
* `certified_radius_robust` — **Theorem B**: within certified radius, margin stays positive
* `advDist_ge_margin_div_L` — distance-to-adversary ≥ margin/L
* `certifiedRadius_is_idempotent` — certified radius satisfies robustness predicate

## Mathematical Context

For an L-Lipschitz score function f with ±1 labels, the worst-case margin under
ε-perturbation degrades by at most Lε. For hinge loss `ℓ(z) = max(0, 1-z)`, the
shifted loss decomposes as:

  `ℓ(m - δ) = ℓ(m) + max(0, δ - max(0, m - 1))`

where `max(0, m - 1)` is the "margin surplus" — the amount by which the margin
exceeds the hinge threshold. The tropical penalty kicks in precisely when the
perturbation budget `δ = Lε` exceeds this surplus.
-/

open Finset BigOperators

noncomputable section

namespace TropAdvTraining

/-! ## Hinge Loss and Margin Surplus -/

/-- Hinge loss: `max 0 (1 - z)`. -/
def hingeLoss (z : ℝ) : ℝ := max 0 (1 - z)

/-- Margin surplus beyond the hinge threshold: `max 0 (z - 1)`. -/
def marginSurplus (z : ℝ) : ℝ := max 0 (z - 1)








/-! ## The Core Algebraic Identity -/

/-
**Key algebraic identity for tropical regularization:**
    `hingeLoss(m - δ) = hingeLoss(m) + max(0, δ - marginSurplus(m))`
    where `marginSurplus(m) = max(0, m - 1)`.

    This decomposes the robust loss (hinge at shifted margin) into the
    empirical loss plus a tropical penalty. The penalty activates when the
    perturbation budget `δ` exceeds the margin surplus.
-/

/-! ## Abstract Definitions -/

/-- Empirical hinge risk: `∑ hingeLoss(mᵢ)`. -/
def empHingeRisk {ι : Type*} (S : Finset ι) (m : ι → ℝ) : ℝ :=
  ∑ i ∈ S, hingeLoss (m i)

/-- Tropical penalty: `∑ max(0, τ - marginSurplus(mᵢ))`. -/
def tropPenalty {ι : Type*} (S : Finset ι) (m : ι → ℝ) (τ : ℝ) : ℝ :=
  ∑ i ∈ S, max 0 (τ - marginSurplus (m i))

/-- Shifted (robust) hinge risk: `∑ hingeLoss(mᵢ - δ)`. -/
def shiftedHingeRisk {ι : Type*} (S : Finset ι) (m : ι → ℝ) (δ : ℝ) : ℝ :=
  ∑ i ∈ S, hingeLoss (m i - δ)

/-! ## Theorem A: The Tropical Regularization Identity -/


/-! ## Metric Space Theorems -/

variable {X : Type*} [PseudoMetricSpace X]

/-- Fixed-label margin: `yval * f(x)` where `yval ∈ {-1, 1}`. -/
def fixedMargin (yval : ℝ) (f : X → ℝ) (x : X) : ℝ := yval * f x





/-! ## Robustness Predicate and Idempotent Closure -/

/-- Robustness predicate: margin stays positive within radius `r`. -/
def RobustAt (yval : ℝ) (f : X → ℝ) (x : X) (r : ℝ) : Prop :=
  ∀ x', dist x x' < r → 0 < fixedMargin yval f x'




/-! ## Tropical Penalty Properties -/




/-! ## Dataset-level Theorems -/





end TropAdvTraining


