-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_jointMeasurementOperator_positive
-- name    : QuantumParallelRepetition.Strategy.jointMeasurementOperator_positive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:48:52.384505+00:00
-- url     : https://prove2.me/theorems/58a7e4e5-be66-48d6-bb20-92c36f8fa5f1
-- title:
--   The joint measurement operator is positive semidefinite
-- statement:
--   For an entangled strategy $S$, questions $x,y$ and answers $a,b$, the joint measurement operator
--
--   $$M^{x,y}_{a,b} \;=\; A^{x}_{a} \otimes B^{y}_{b}$$
--
--   is positive semidefinite, where $A^{x}_{a}$ is Alice's measurement operator for answer $a$ on question $x$ and $B^{y}_{b}$ is Bob's for answer $b$ on question $y$. The Kronecker product of two positive semidefinite matrices is positive semidefinite, and each factor is positive by the POVM axioms.
--
--   Together with nonnegativity of the trace pairing this is what makes the quantity $\operatorname{tr}(\rho\, M^{x,y}_{a,b})$ a genuine probability.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L133-L136

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.jointMeasurementOperator_positive
    (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointMeasurementOperator x y a b).PosSemidef := by sorry
