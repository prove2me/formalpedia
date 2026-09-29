-- Prove2me | solution 1 for GrokkingPhaseTransition.delayed_transition_positive_branches
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:50:28.122706+00:00
-- url     : https://prove2.me/submissions/af158f8d-a1a9-4fd4-a769-076265910089

-- Sol generated from MachineLearning/GrokkingPhaseTransition.lean
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




/-- Before (and at) the prescribed delay, the network's test score is zero. -/
theorem grokNetwork_before (delay time : ℝ) (h : time ≤ delay) :
    grokNetwork delay time = 0 := by
  unfold grokNetwork twoLayerScalar
  rw [max_eq_right]
  · ring
  · linarith

/-- Delayed generalization for the explicit two-layer network: it fails to
Generalize through the delay, then generalizes at every later time. -/
theorem delayed_generalization (delay : ℝ) :
    (∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time) := by
  constructor
  · intro time htime
    rw [Generalizes, grokNetwork_before delay time htime]
    exact lt_irrefl 0
  · intro time htime
    unfold Generalizes grokNetwork twoLayerScalar
    rw [max_eq_left]
    · linarith
    · linarith



/-- The delayed transition can be packaged with the degenerate equilibrium at
its critical parameter. -/
theorem delayed_transition_has_critical_equilibrium (delay : ℝ) :
    ((∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time)) ∧
      IsEquilibrium 0 0 := by
  refine ⟨delayed_generalization delay, ?_⟩
  norm_num [IsEquilibrium, saddleNodeField]

/-- Before the saddle-node critical parameter there are no equilibria.  This
extends the preceding delayed-transition package by its negative regime. -/
theorem delayed_transition_negative_regime (delay : ℝ) :
    (((∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time)) ∧
      IsEquilibrium 0 0) ∧
      (∀ parameter < 0, ∀ state, ¬ IsEquilibrium parameter state) := by
  refine ⟨delayed_transition_has_critical_equilibrium delay, ?_⟩
  intro parameter hparameter state heq
  unfold IsEquilibrium saddleNodeField at heq
  nlinarith [sq_nonneg state]

/-- At the critical parameter, zero is the unique equilibrium.  This adds the
critical uniqueness statement to the negative-regime result. -/
theorem delayed_transition_critical_unique (delay : ℝ) :
    ((((∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time)) ∧
      IsEquilibrium 0 0) ∧
      (∀ parameter < 0, ∀ state, ¬ IsEquilibrium parameter state)) ∧
      (∀ state, IsEquilibrium 0 state ↔ state = 0) := by
  refine ⟨delayed_transition_negative_regime delay, ?_⟩
  intro state
  unfold IsEquilibrium saddleNodeField
  constructor
  · intro h
    nlinarith [sq_nonneg state]
  · rintro rfl
    norm_num




open GrokkingPhaseTransition in
theorem solution(delay : ℝ) :
    (((((∀ time ≤ delay, ¬ Generalizes delay time) ∧
      (∀ time, delay < time → Generalizes delay time)) ∧
      IsEquilibrium 0 0) ∧
      (∀ parameter < 0, ∀ state, ¬ IsEquilibrium parameter state)) ∧
      (∀ state, IsEquilibrium 0 state ↔ state = 0)) ∧
      (∀ parameter, 0 < parameter → ∀ state,
        IsEquilibrium parameter state ↔
          state = Real.sqrt parameter ∨ state = -Real.sqrt parameter) := by
  refine ⟨delayed_transition_critical_unique delay, ?_⟩
  intro parameter hparameter state
  have hsqrt : (Real.sqrt parameter) ^ 2 = parameter := by
    exact Real.sq_sqrt (le_of_lt hparameter)
  unfold IsEquilibrium saddleNodeField
  constructor
  · intro heq
    have hfactor : (state - Real.sqrt parameter) *
        (state + Real.sqrt parameter) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      linarith
    · right
      linarith
  · intro hstate
    rcases hstate with rfl | rfl <;> nlinarith
