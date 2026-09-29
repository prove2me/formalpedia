-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_outcomeProbability_nonneg
-- name    : QuantumParallelRepetition.Strategy.outcomeProbability_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:49:34.464296+00:00
-- url     : https://prove2.me/theorems/d50e2837-973e-4aed-ace9-85cff1338169
-- title:
--   Born-rule outcome probabilities are nonnegative
-- statement:
--   The probability that an entangled strategy $S$ produces the answer pair $(a,b)$ on the question pair $(x,y)$ is nonnegative:
--
--   $$\Pr[a,b \mid x,y] \;=\; \operatorname{Re}\operatorname{tr}\!\left(\rho\, (A^{x}_{a} \otimes B^{y}_{b})\right) \;\ge\; 0 ,$$
--
--   where $\rho$ is the shared state. This is the Born rule applied to the joint measurement operator, and it follows by pairing the positivity of $\rho$ with the positivity of $A^{x}_{a} \otimes B^{y}_{b}$.
--
--   It is the first of the two facts — nonnegativity and normalisation — that make the outcome distribution of a strategy an actual probability distribution.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L141-L145

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.outcomeProbability_nonneg
    (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by sorry
