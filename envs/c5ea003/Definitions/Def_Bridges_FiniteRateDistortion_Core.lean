-- Prove2me | Definitions.Def_Bridges_FiniteRateDistortion_Core
-- name    : Bridges_FiniteRateDistortion_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:32.065529+00:00
-- url     : https://prove2.me/theorems/97d22d13-fbd3-456a-a275-2dd39631579b
-- title:
--   Aether Catalog definitions — Bridges_FiniteRateDistortion_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FiniteRateDistortion.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FiniteRateDistortion/Core.lean by skeleton subtraction
import Mathlib

/-!
# Finite rate–distortion theory: channels, mutual information, and the Lagrangian dual

This module supplies the objects used by
`Bridges/FiniteRateDistortion/TropicalEnvelope.lean`, which referred to a finite
rate-distortion vocabulary that no module in the catalog provided.

Everything is finite and elementary:

* `FinProbDist α`, `Channel α β` — a source distribution and a test channel;
* `mutualInfo`, `distortion` — the two functionals of a channel;
* `rateDistortion μ d D` — the infimum of the mutual information over channels meeting
  the distortion constraint;
* `lagrangianDual μ d s` — the infimum of `I(W) + s · d(W)`;
* `lagrangianDual_le_rateDistortion` — **weak duality**: `Φ(s) - s·D ≤ R(D)` for every
  slope `s ≥ 0`, the affine lower bound whose tropical envelope is studied downstream.

The only analytic input is the elementary estimate `w · log (w / q) ≥ -q/e`
(`neg_div_exp_one_le_mul_log_div`), which makes the Lagrangian set bounded below, so the
infima are genuine.
-/

open Finset

noncomputable section

namespace FiniteRateDistortion

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## Sources and channels -/

/-- A probability distribution on a finite alphabet. -/
structure FinProbDist (α : Type*) [Fintype α] where
  /-- The probability mass. -/
  mass : α → ℝ
  /-- Masses are nonnegative. -/
  mass_nonneg : ∀ a, 0 ≤ mass a
  /-- Masses sum to one. -/
  mass_sum_one : ∑ a, mass a = 1

/-- A test channel from `α` to `β`: a stochastic matrix. -/
structure Channel (α β : Type*) [Fintype α] [Fintype β] where
  /-- Transition probabilities. -/
  prob : α → β → ℝ
  /-- Transition probabilities are nonnegative. -/
  prob_nonneg : ∀ a b, 0 ≤ prob a b
  /-- Each row sums to one. -/
  prob_sum_one : ∀ a, ∑ b, prob a b = 1

/-- The output distribution induced by a source and a channel. -/
def outMass (μ : FinProbDist α) (W : Channel α β) (b : β) : ℝ :=
  ∑ a, μ.mass a * W.prob a b




/-! ## The elementary entropy estimate -/



/-! ## Mutual information and distortion -/

/-- The mutual information of a source and a test channel. -/
def mutualInfo (μ : FinProbDist α) (W : Channel α β) : ℝ :=
  ∑ a, ∑ b, μ.mass a * W.prob a b * Real.log (W.prob a b / outMass μ W b)


/-- The expected distortion of a test channel. -/
def distortion (μ : FinProbDist α) (d : α → β → ℝ) (W : Channel α β) : ℝ :=
  ∑ a, ∑ b, μ.mass a * W.prob a b * d a b

/-- A crude a-priori bound on the size of the distortion measure. -/
def distortionBudget (d : α → β → ℝ) : ℝ := ∑ a, ∑ b, |d a b|


/-! ## The rate–distortion function and its Lagrangian dual -/

/-- A distortion level is feasible when some channel achieves it. -/
def FeasibleDistortion (μ : FinProbDist α) (d : α → β → ℝ) (D : ℝ) : Prop :=
  ∃ W : Channel α β, distortion μ d W ≤ D

/-- The set of achievable rates at distortion level `D`. -/
def rateDistortionSet (μ : FinProbDist α) (d : α → β → ℝ) (D : ℝ) : Set ℝ :=
  {r | ∃ W : Channel α β, distortion μ d W ≤ D ∧ mutualInfo μ W = r}

/-- The rate–distortion function. -/
def rateDistortion (μ : FinProbDist α) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf (rateDistortionSet μ d D)

/-- The set of Lagrangian values at slope `s`. -/
def lagrangianDualSet (μ : FinProbDist α) (d : α → β → ℝ) (s : ℝ) : Set ℝ :=
  {r | ∃ W : Channel α β, mutualInfo μ W + s * distortion μ d W = r}

/-- The Lagrangian dual value at slope `s`. -/
def lagrangianDual (μ : FinProbDist α) (d : α → β → ℝ) (s : ℝ) : ℝ :=
  sInf (lagrangianDualSet μ d s)



end FiniteRateDistortion


