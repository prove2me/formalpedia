-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_nonneg
-- name    : QuantumParallelRepetition.entangledValue_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-09T19:56:07.623199+00:00
-- url     : https://prove2.me/theorems/ed0b300e-c1cb-4071-ab61-b4b7433ac7e8
-- title:
--   The entangled value of a game is nonnegative
-- statement:
--   The entangled value of a finite two-player game is nonnegative:
--
--   $$\omega^{*}(G) \;=\; \sup_{S} \omega(S) \;\ge\; 0 .$$
--
--   If some strategy exists, its winning probability is a nonnegative member of the set whose supremum is being taken, and the set is bounded above; if the answer alphabets admit no strategy at all the range is empty and the real supremum is $0$ by convention. Both cases give the bound.
--
--   This is one half of $0 \le \omega^{*}(G) \le 1$, and it is the fact that turns an exponentially decaying upper bound on the repeated entangled value into convergence to zero, by squeezing between the two.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L241-L249

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open QuantumParallelRepetition
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.entangledValue_nonneg (G : Game X Y A B) :
    0 ≤ entangledValue G := by sorry
