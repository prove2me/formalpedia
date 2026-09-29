-- Prove2me | Theorems.Thm_QuantumParallelRepetition_entangledValue_exponential_decay
-- name    : QuantumParallelRepetition.entangledValue_exponential_decay
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-08-09T03:16:48.886415+00:00
-- url     : https://prove2.me/theorems/e18d53d3-db05-49b5-86a5-3154da376483
-- statement:
--   Let $G$ be a finite two-player one-round game with nonempty answer alphabets and entangled value $\omega^*(G)<1$. The exponential parallel-repetition theorem asserts that there are constants $C>0$ and $c>0$, depending only on $G$, such that every repetition count $n$ satisfies
--
--   $$
--   \omega^*(G^n)\le C e^{-cn}.
--   $$
--
--   This is stronger than polynomial decay. The general theorem was recently established by OpenAI; this abstract milestone supports formalization of that argument as well as alternative, more modular, or quantitatively sharper proofs.
--
--   **Formalization Note** The bound includes $n=0$, where it simply requires the zero-fold repeated value to be at most $C$.
-- source:
--   OpenAI, Ten Advances in Mathematics and Theoretical Computer Science, Chapter 6, Theorem 1.1, pp. 154–155, 2026, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; Lean certificate: https://github.com/openai/ten-proofs/blob/main/QuantumParallelRepetition.lean; earlier general polynomial bound: Henry Yuen, arXiv:1604.04340v1, Theorem 1.

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Analysis.SpecialFunctions.Exp

namespace QuantumParallelRepetition

/-- Exponential parallel repetition for finite two-player entangled games.
The constants may depend on the game. -/
theorem entangledValue_exponential_decay
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B]
    (G : Game X Y A B)
    (hG : entangledValue G < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      repeatedEntangledValue G n ≤ C * Real.exp (-c * n) := by
  sorry

end QuantumParallelRepetition
