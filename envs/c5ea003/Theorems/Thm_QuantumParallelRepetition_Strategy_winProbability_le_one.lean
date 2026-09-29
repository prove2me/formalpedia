-- Prove2me | Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_le_one
-- name    : QuantumParallelRepetition.Strategy.winProbability_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:52:54.727373+00:00
-- url     : https://prove2.me/theorems/17570be4-4be1-4edf-83d7-5e038d97205c
-- title:
--   The winning probability of a strategy is at most one
-- statement:
--   No entangled strategy wins a game with probability greater than one:
--
--   $$\omega(S) \;=\; \sum_{x,y} \mu(x,y) \sum_{a,b} V(x,y,a,b)\,\Pr[a,b \mid x,y] \;\le\; 1 .$$
--
--   For each fixed question pair the accepting answer pairs contribute at most the full outcome distribution, which sums to one; averaging over the normalised question distribution $\mu$ therefore gives at most one.
--
--   This is the bound that makes the set of achievable winning probabilities bounded above, so that the entangled value can be defined as a supremum.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L187-L215

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

theorem QuantumParallelRepetition.Strategy.winProbability_le_one
    (S : Strategy G) : S.winProbability ≤ 1 := by sorry
