-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.outcomeProbability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-09T19:49:35.395046+00:00
-- url     : https://prove2.me/submissions/eb45999c-237e-4396-a338-d5e0493a3d90

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Theorems.Thm_QuantumParallelRepetition_trace_mul_posSemidef_nonneg
import Theorems.Thm_QuantumParallelRepetition_Strategy_jointMeasurementOperator_positive

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

open QuantumParallelRepetition.Strategy in
theorem solution
    (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by
  exact QuantumParallelRepetition.trace_mul_posSemidef_nonneg S.state.positive
    (S.jointMeasurementOperator_positive x y a b)
