-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
-- name    : QuantumParallelRepetition.exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T14:17:24.36129+00:00
-- url     : https://prove2.me/theorems/f1c02e08-173d-4cb3-8794-775750c8133b
-- title:
--   Averaging over seeds leaves the conditional law of the next question at a marked history unchanged
-- statement:
--   Keep the setting above, with at least one coordinate free. Fix a seed $s$ — a distinguished free coordinate together with a two-sided partition of the free coordinates, orderings and cuts — let $\Sigma$ be the right side it determines, and let $k$ be the rank of the seed's own coordinate inside $\Sigma$. For an arbitrary reference outcome of $G^n$, let $c$ be the marked history context that $s$ and that outcome produce. Then the conditional distribution of the next Alice question given $c$, computed from the seed-averaged reverse-Bob joint law, coincides with the conditional distribution given $c$ computed from the single fixed seed $s$ under the postselected outcome law $\Pr[\,\cdot \mid \text{every coordinate of } D \text{ is won}\,]$. Averaging over the seed therefore costs nothing once the history context is fixed.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L56827-L56971

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Theorems.Thm_QuantumParallelRepetition_exactReverseRightSide_coordinate_mem
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextJoint
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) := by sorry
