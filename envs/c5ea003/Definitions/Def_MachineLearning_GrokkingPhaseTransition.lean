-- Prove2me | Definitions.Def_MachineLearning_GrokkingPhaseTransition
-- name    : MachineLearning_GrokkingPhaseTransition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:43:36.632887+00:00
-- url     : https://prove2.me/theorems/ad1198da-bfb6-4f21-9417-22c7d755c14e
-- title:
--   Aether Catalog definitions — MachineLearning_GrokkingPhaseTransition
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.GrokkingPhaseTransition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/GrokkingPhaseTransition.lean by skeleton subtraction
import Mathlib

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

namespace GrokkingPhaseTransition

/-- A scalar two-layer, width-one ReLU network. -/
def twoLayerScalar (inputWeight hiddenBias outputWeight outputBias x : ℝ) : ℝ :=
  outputWeight * max (inputWeight * x + hiddenBias) 0 + outputBias

/-- The explicit trajectory used for the delayed-generalization model. -/
def grokNetwork (delay time : ℝ) : ℝ :=
  twoLayerScalar 1 (-delay) 1 0 time

/-- Generalization means that the scalar test score is strictly positive. -/
def Generalizes (delay time : ℝ) : Prop := 0 < grokNetwork delay time



/-- The standard one-dimensional saddle-node vector field. -/
def saddleNodeField (parameter state : ℝ) : ℝ := parameter - state ^ 2

/-- A state is an equilibrium when the saddle-node vector field vanishes. -/
def IsEquilibrium (parameter state : ℝ) : Prop := saddleNodeField parameter state = 0






end GrokkingPhaseTransition


