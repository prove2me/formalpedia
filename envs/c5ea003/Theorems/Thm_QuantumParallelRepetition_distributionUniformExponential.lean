-- Prove2me | Theorems.Thm_QuantumParallelRepetition_distributionUniformExponential
-- name    : QuantumParallelRepetition.distributionUniformExponential
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T01:52:53.1442+00:00
-- url     : https://prove2.me/theorems/ee9dcd81-daeb-4c1b-8962-95bd3bd1ae25
-- title:
--   Exponential decay of the entangled value under parallel repetition, with an explicit rate
-- statement:
--   There is an absolute constant $c>0$, independent of the game, with the following property. Let $G$ be a two-player one-round game with finite question alphabets $X,Y$ and finite nonempty answer alphabets $A,B$, and suppose $G$ cannot be won perfectly by entangled players, i.e. $\omega^*(G)<1$. Then for every $n\ge 1$ the entangled value of the $n$-fold parallel repetition satisfies
--   $$\omega^*\big(G^{\otimes n}\big)\;\le\;\exp\!\left(-\,c\,\frac{\big(1-\omega^*(G)\big)^{13}}{\big(1-\omega^*(G)\big)+\log\big(|A|\cdot|B|\big)}\;n\right).$$
--   Thus the value decays exponentially in the number of repetitions, at a rate polynomial in the gap $1-\omega^*(G)$ and inversely logarithmic in the size of the answer alphabets; crucially, the constant $c$ is uniform over all games, so the bound is a genuine quantitative parallel-repetition theorem rather than a game-by-game statement.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L70957-L70973

import Definitions.Def_quantum_parallel_repetition_game
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

theorem QuantumParallelRepetition.distributionUniformExponential :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) := by sorry
