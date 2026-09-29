-- Prove2me | Theorems.Thm_QuantumParallelRepetition_pdf_distributionUniformExponential_of_uniform_source_rounding
-- name    : QuantumParallelRepetition.pdf_distributionUniformExponential_of_uniform_source_rounding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T19:02:35.014401+00:00
-- url     : https://prove2.me/theorems/b8efea90-e44c-468b-b8d4-f835fd9c0588
-- title:
--   Exponential decay of the entangled value under parallel repetition, conditional on uniform rounding
-- statement:
--   Assume the *uniform rounding hypothesis*: there is a constant $K \ge 1$ such that for every finite game $G$, every
--   $n$, every strategy $S$ for $G^{\otimes n}$, and every coordinate set $D$ with a remaining coordinate and positive
--   postselection mass, if the uniform remaining failure of $S$ on $D$ is below $(1-\omega^*(G))/2$, then for all
--   $\alpha \in (0,1]$ and $\gamma > 0$ there is a single-copy strategy for $G$ whose winning probability is at least
--   the rounded lower bound $1 - \frac{1-\omega^*(G)}{2} - \mathrm{Loss}\bigl(K,\alpha,\text{martingale rate},\ \mathrm{Pinsker}+\gamma\bigr)$.
--   Then there is an absolute constant $c > 0$ such that for every finite game $G$ with nonempty answer sets and
--   $\omega^*(G) < 1$, and every $n \ge 1$,
--   $$\omega^*\bigl(G^{\otimes n}\bigr) \;\le\; \exp\!\left(-\,c\,\frac{\bigl(1-\omega^*(G)\bigr)^{13}}{\bigl(1-\omega^*(G)\bigr) + \log\bigl(|A|\,|B|\bigr)}\; n\right).$$
--   This is the parallel repetition theorem for entangled games in the form delivered by this development: the value
--   decays exponentially at a rate polynomial in the gap $1-\omega^*(G)$ and inversely logarithmic in the answer
--   alphabet sizes.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L67765-L67911

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

theorem QuantumParallelRepetition.pdf_distributionUniformExponential_of_uniform_source_rounding
    (rounding :
      ∃ K : ℝ, 1 ≤ K ∧
        ∀ {X Y A B : Type}
          [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
          (G : Game X Y A B)
          (n : ℕ) (S : Strategy (G.repeat n))
          (D : Finset (Fin n)),
          0 < (Finset.univ \ D).card →
          0 < repeatedPostselectionMass G n S D →
          ∀ (alpha gamma : ℝ),
            0 < alpha → alpha ≤ 1 → 0 < gamma →
            uniformRemainingFailure
                (strategyEventLaw (G.repeat n) S)
                (repeatedCoordinateWin G n) D <
              (1 - entangledValue G) / 2 →
            ∃ rounded : Strategy G,
              roundedWinningLowerBound (1 - entangledValue G)
                  K alpha (martingaleRate G n S D)
                  (exactSourcePinskerRate G n S D + gamma) ≤
                rounded.winProbability) :
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
