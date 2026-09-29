-- Prove2me | Definitions.Def_MachineLearning_PolicyGradient_Theorems
-- name    : MachineLearning_PolicyGradient_Theorems
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:52:49.013072+00:00
-- url     : https://prove2.me/theorems/8b2a5183-d9e1-468a-93e6-a0fbf6b8d255
-- title:
--   Aether Catalog definitions — MachineLearning_PolicyGradient_Theorems
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PolicyGradient.Theorems`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PolicyGradient/Theorems.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Finite policy-gradient and exploration-variance theorems

A self-contained finite-action formalization. Policies are differentiable
families of probability vectors. The score identity is represented without
logs by `∂p(a) = p(a) ψ(a)`.
-/

namespace PolicyGradient

open scoped BigOperators

variable {n d : ℕ}

/-- Finite expectation with respect to a weight vector. -/
def expect (p f : Fin n → ℝ) : ℝ := ∑ a, p a * f a

/-- The second moment of a scalar importance-weighted estimator. -/
noncomputable def importanceSecondMoment (behavior target g : Fin n → ℝ) : ℝ :=
  ∑ a, behavior a * (target a / behavior a * g a) ^ 2








end PolicyGradient


