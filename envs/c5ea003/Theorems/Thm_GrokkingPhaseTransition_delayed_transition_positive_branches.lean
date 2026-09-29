-- Prove2me | Theorems.Thm_GrokkingPhaseTransition_delayed_transition_positive_branches
-- name    : GrokkingPhaseTransition.delayed_transition_positive_branches
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:33:22.35446+00:00
-- url     : https://prove2.me/theorems/156b3dae-357f-4535-930a-e3bb5a1bd3ea
-- title:
--   After the critical parameter, the two equilibrium branches are exactly
-- statement:
--   After the critical parameter, the two equilibrium branches are exactly
--   `±√parameter`.  This is the positive regime of the saddle-node.
--
--   ```lean
--   theorem GrokkingPhaseTransition.delayed_transition_positive_branches(delay : ℝ) :
--       (((((∀ time ≤ delay, ¬ Generalizes delay time) ∧
--         (∀ time, delay < time → Generalizes delay time)) ∧
--         IsEquilibrium 0 0) ∧
--         (∀ parameter < 0, ∀ state, ¬ IsEquilibrium parameter state)) ∧
--         (∀ state, IsEquilibrium 0 state ↔ state = 0)) ∧
--         (∀ parameter, 0 < parameter → ∀ state,
--           IsEquilibrium parameter state ↔
--             state = Real.sqrt parameter ∨ state = -Real.sqrt parameter) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/GrokkingPhaseTransition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/GrokkingPhaseTransition.lean#L95

-- Thm stub generated from MachineLearning/GrokkingPhaseTransition.lean
import Mathlib
import Definitions.Def_MachineLearning_GrokkingPhaseTransition

/-!
# Grokking as a delayed ReLU transition and a saddle-node bifurcation

This file gives a minimal, fully proved model of delayed generalization in a
width-one, two-layer ReLU network.  Its scalar output stays exactly zero up to a
prescribed delay and becomes strictly positive afterwards.  The same threshold
is paired with the standard saddle-node normal form `μ - x²`; its equilibria
change from none, to one degenerate equilibrium, to two branches.

The model is deliberately small: it isolates the phase-transition mechanism
without claiming that arbitrary training procedures exhibit grokking.
-/

open GrokkingPhaseTransition

theorem GrokkingPhaseTransition.delayed_transition_positive_branches(delay : ℝ) :
    (((((∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time)) ∧
      IsEquilibrium 0 0) ∧
      (∀ parameter < 0, ∀ state, ¬ IsEquilibrium parameter state)) ∧
      (∀ state, IsEquilibrium 0 state ↔ state = 0)) ∧
      (∀ parameter, 0 < parameter → ∀ state,
        IsEquilibrium parameter state ↔
          state = Real.sqrt parameter ∨ state = -Real.sqrt parameter) := by sorry
