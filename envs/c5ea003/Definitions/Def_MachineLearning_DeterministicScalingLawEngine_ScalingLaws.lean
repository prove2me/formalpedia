-- Prove2me | Definitions.Def_MachineLearning_DeterministicScalingLawEngine_ScalingLaws
-- name    : MachineLearning_DeterministicScalingLawEngine_ScalingLaws
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:44.369217+00:00
-- url     : https://prove2.me/theorems/5cf459f0-2c20-434e-b780-61e160da7104
-- title:
--   Aether Catalog definitions — MachineLearning_DeterministicScalingLawEngine_ScalingLaws
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.DeterministicScalingLawEngine.ScalingLaws`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/DeterministicScalingLawEngine/ScalingLaws.lean by skeleton subtraction
import Mathlib

/-!
# Deterministic scaling-law engine from two-sided polynomial tail bounds

This file develops a minimal, fully-compiling deterministic scaling-law engine
built from two-sided polynomial tail bounds on a loss function `L : ℕ → ℝ`.

A `TailBounds` packages a loss function together with constants `c < C` and a
decay exponent `α > 0` such that, for all `n ≥ 1`,
`c * n ^ (-α) ≤ L n ≤ C * n ^ (-α)`.

From these bounds we derive five elementary consequences relating capacity
(the index `n`, e.g. number of samples / parameters) to the achievable loss `ε`.
-/

namespace ScalingLaws

/-- Two-sided polynomial tail bounds on a loss function. -/
structure TailBounds where
  /-- The loss function. -/
  L : ℕ → ℝ
  /-- The polynomial decay exponent. -/
  α : ℝ
  /-- The lower constant. -/
  c : ℝ
  /-- The upper constant. -/
  C : ℝ
  /-- The decay exponent is positive. -/
  α_pos : 0 < α
  /-- The lower constant is positive. -/
  c_pos : 0 < c
  /-- The lower constant is strictly below the upper constant. -/
  c_lt_C : c < C
  /-- Lower tail bound. -/
  lower : ∀ n : ℕ, n ≥ 1 → c * (n : ℝ) ^ (-α) ≤ L n
  /-- Upper tail bound. -/
  upper : ∀ n : ℕ, n ≥ 1 → L n ≤ C * (n : ℝ) ^ (-α)

variable (tb : TailBounds)






end ScalingLaws


