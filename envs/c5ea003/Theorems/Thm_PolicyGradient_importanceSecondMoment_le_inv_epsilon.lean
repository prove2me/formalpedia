-- Prove2me | Theorems.Thm_PolicyGradient_importanceSecondMoment_le_inv_epsilon
-- name    : PolicyGradient.importanceSecondMoment_le_inv_epsilon
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:49:46.307556+00:00
-- url     : https://prove2.me/theorems/08768f3d-99f5-48f1-9391-2382399fea12
-- title:
--   Exact `O(1/ε)` second-moment bound for importance weighting.
-- statement:
--   Exact `O(1/ε)` second-moment bound for importance weighting. The condition
--   `behavior ≥ ε·target` includes ε-greedy exploration relative to a target
--   policy, and the constant is explicit.
--
--   ```lean
--   theorem PolicyGradient.importanceSecondMoment_le_inv_epsilon    (behavior target g : Fin n → ℝ) (ε : ℝ)
--       (hε : 0 < ε) (hb : ∀ a, 0 < behavior a)
--       (ht : ∀ a, 0 ≤ target a)
--       (hexplore : ∀ a, ε * target a ≤ behavior a) :
--       importanceSecondMoment behavior target g ≤
--         (1 / ε) * expect target (fun a => (g a) ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PolicyGradient/Theorems.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PolicyGradient/Theorems.lean#L86

-- Thm stub generated from MachineLearning/PolicyGradient/Theorems.lean
import Mathlib
import Definitions.Def_MachineLearning_PolicyGradient_Theorems
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Finite policy-gradient and exploration-variance theorems

A self-contained finite-action formalization. Policies are differentiable
families of probability vectors. The score identity is represented without
logs by `∂p(a) = p(a) ψ(a)`.
-/

open PolicyGradient

open scoped BigOperators

variable {n d : ℕ}

theorem PolicyGradient.importanceSecondMoment_le_inv_epsilon    (behavior target g : Fin n → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hb : ∀ a, 0 < behavior a)
    (ht : ∀ a, 0 ≤ target a)
    (hexplore : ∀ a, ε * target a ≤ behavior a) :
    importanceSecondMoment behavior target g ≤
      (1 / ε) * expect target (fun a => (g a) ^ 2) := by sorry
