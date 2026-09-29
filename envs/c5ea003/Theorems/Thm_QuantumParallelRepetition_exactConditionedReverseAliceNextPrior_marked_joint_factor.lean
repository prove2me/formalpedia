-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactConditionedReverseAliceNextPrior_marked_joint_factor
-- name    : QuantumParallelRepetition.exactConditionedReverseAliceNextPrior_marked_joint_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T13:37:46.481215+00:00
-- url     : https://prove2.me/theorems/6870b6de-decc-45d4-973c-1bfc3d032df1
-- title:
--   The reverse-Alice prior factors: the next question follows the game's conditional distribution
-- statement:
--   Fix a side $\Sigma \subseteq \bar D$, a default letter $y_0 \in Y$ and a marker position $k < |\Sigma|$, and assume $|\bar D| > 0$. Let $\Pi$ be the reverse-Alice next prior for the side $\Sigma$: the uniform-flag reference over the pushforward, under Alice's reverse projection, of the product of the reverse-Alice conditional seed law with the strategy's *unconditioned* outcome law. Group $\Pi$ by the code sending a flagged context to the pair (its prefix mask at $k$, its $k$-th $Y$-letter), obtaining a law $\Pi_k$ on (masked context, next letter). Then for every masked context $c$ and every $y \in Y$,
--   $$\Pi_k(c, y) \;=\; \mu\big(y \mid x_c\big)\cdot \Pi_k^{(1)}(c),$$
--   where $\Pi_k^{(1)}$ is the first marginal of $\Pi_k$ and $x_c$ is the Alice question that $c$ records at the side position of rank $k$. Equivalently: under the prior, conditionally on the masked context, the next Bob question is distributed exactly as the game's conditional $\mu(\cdot \mid x)$ for the matching Alice question.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L55289-L55399

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactConditionedReverseAliceNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (next : Y) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalYGivenX
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          target := by sorry
