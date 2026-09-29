-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactConditionedReverseBobNextPrior_marked_joint_factor
-- name    : QuantumParallelRepetition.exactConditionedReverseBobNextPrior_marked_joint_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T14:16:54.01219+00:00
-- url     : https://prove2.me/theorems/53993802-2f2c-43c6-84ae-0274b68d55d4
-- title:
--   The marked next-question prior factors as the game's conditional question distribution
-- statement:
--   Fix a game $G$ with question distribution $\mu$ on $X \times Y$, an integer $n$, a strategy for the $n$-fold repetition $G^n$, a set $D \subseteq [n]$ of already conditioned coordinates leaving at least one coordinate free, a subset $\Sigma$ of the free coordinates, a default letter $x_0 \in X$, and a rank $k$ inside $\Sigma$ (the *marker*). Consider the reverse-Bob *prior* on masked records, and push it forward along the map that sends a record to the pair consisting of its prefix mask at $k$ and the Alice question stored in slot $k$. The theorem states that for every masked context $c$ and every $x \in X$ this grouped joint mass factors as
--   $$
--   \Pr[\,c,\,x\,] \;=\; \mu(x \mid y_c)\cdot \Pr[\,c\,],
--   $$
--   where $y_c$ is the Bob question that $c$ records at the coordinate of rank $k$, $\mu(x \mid y) = \mu(x,y)/\mu_Y(y)$ is the game's conditional question distribution, and $\Pr[c]$ is the first marginal of the same grouped mass. In words: under the prior, the Alice question revealed next is distributed exactly as $\mu(\cdot \mid y_c)$ and is independent of everything the context already records.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L56507-L56617

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

theorem QuantumParallelRepetition.exactConditionedReverseBobNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (target : ExactReverseBobNextContext X Y A B D side)
    (next : X) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalXGivenY
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseBobNextPrior
              G n S D remaining side))
          target := by sorry
