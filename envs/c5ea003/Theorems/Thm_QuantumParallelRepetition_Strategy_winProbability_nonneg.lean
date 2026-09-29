-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_nonneg
-- name    : QuantumParallelRepetition.Strategy.winProbability_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:52:12.734563+00:00
-- url     : https://prove2.me/theorems/b992baa8-8874-451f-8a77-c3c2ac27a0fc
-- title:
--   The winning probability of a strategy is nonnegative
-- statement:
--   The winning probability of an entangled strategy $S$ for a game $G$,
--
--   $$\omega(S) \;=\; \sum_{x,y} \mu(x,y) \sum_{a,b} V(x,y,a,b)\,\Pr[a,b \mid x,y] ,$$
--
--   is nonnegative. Each term is a product of a nonnegative question weight $\mu(x,y)$ with a sum of outcome probabilities restricted to the accepting answer pairs, and both factors are nonnegative.
--
--   This is the lower half of the bracket $0 \le \omega(S) \le 1$ that makes the entangled value of a game a well-defined real number.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L180-L185

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.winProbability_nonneg
    (S : Strategy G) : 0 ≤ S.winProbability := by sorry
