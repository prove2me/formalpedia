-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_tendsto_zero
-- name    : QuantumParallelRepetition.entangledValue_tendsto_zero
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-08-09T03:16:58.386832+00:00
-- url     : https://prove2.me/theorems/5d4a9804-19de-4ef4-8c84-8e1d9d8584db
-- statement:
--   Let $G$ be a finite two-player one-round game with nonempty answer alphabets, and let $\omega^*(G)$ be the supremal winning probability of its finite-dimensional entangled strategies. Let $G^n$ denote the $n$-fold parallel repetition, in which the referee samples all coordinates independently and the players win only if every coordinate accepts.
--
--   If the original game cannot be won with certainty,
--
--   $$
--   \omega^*(G)<1,
--   $$
--
--   then its repeated entangled value converges to zero:
--
--   $$
--   \lim_{n\to\infty}\omega^*(G^n)=0.
--   $$
--
--   Equivalently, for every $\varepsilon>0$, all sufficiently large repetition counts $n$ satisfy $\omega^*(G^n)<\varepsilon$. The theorem deliberately asserts no rate of convergence.
--
--   **Formalization Note** Lean expresses the conclusion as `Tendsto (repeatedEntangledValue G) atTop (𝓝 0)`. The sequence includes the zero-fold repetition, but changing finitely many terms does not affect its limit.
-- source:
--   Henry Yuen, A parallel repetition theorem for all entangled games, arXiv:1604.04340v1, p. 2, qualitative consequence immediately before Theorem 1 and p. 1, abstract, https://arxiv.org/abs/1604.04340

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Topology.Order.Basic

open Filter
open scoped Topology

namespace QuantumParallelRepetition

/-- The entangled value of every nontrivial finite two-player game tends to zero under
parallel repetition. -/
theorem entangledValue_tendsto_zero
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Game X Y A B)
    (hG : entangledValue G < 1) :
    Tendsto (repeatedEntangledValue G) atTop (𝓝 0) := by
  sorry

end QuantumParallelRepetition
