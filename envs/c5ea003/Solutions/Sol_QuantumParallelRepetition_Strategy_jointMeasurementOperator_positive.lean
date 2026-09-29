-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.jointMeasurementOperator_positive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-09T19:48:53.317558+00:00
-- url     : https://prove2.me/submissions/26f3efe6-29c6-4573-b82e-fab41a5d643c

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

open QuantumParallelRepetition.Strategy in
theorem solution
    (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointMeasurementOperator x y a b).PosSemidef := by
  exact ((S.aliceMeasurement x).positive a).kronecker
    ((S.bobMeasurement y).positive b)
