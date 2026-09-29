-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.winProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-09T19:52:13.533493+00:00
-- url     : https://prove2.me/submissions/6174924f-87b3-45b0-9712-7b494f8105ab

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Theorems.Thm_QuantumParallelRepetition_Strategy_outcomeProbability_nonneg

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

open QuantumParallelRepetition.Strategy in
theorem solution
    (S : Strategy G) : 0 ≤ S.winProbability := by
  unfold Strategy.winProbability
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  apply mul_nonneg (G.weight_nonneg x y)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split <;> simp [S.outcomeProbability_nonneg]
