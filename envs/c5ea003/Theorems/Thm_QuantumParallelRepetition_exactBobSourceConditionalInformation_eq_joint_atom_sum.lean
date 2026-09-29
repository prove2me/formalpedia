-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactBobSourceConditionalInformation_eq_joint_atom_sum
-- name    : QuantumParallelRepetition.exactBobSourceConditionalInformation_eq_joint_atom_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T13:27:18.860431+00:00
-- url     : https://prove2.me/theorems/316d3350-db36-4348-9ad8-3b069405002f
-- title:
--   Bob's conditional source information as a sum over postselected joint outcomes
-- statement:
--   This is the mirror of the previous statement. Assume $|\bar D| > 0$ and that the postselection mass is positive, and fix a base history flag $r_0$. Then Bob's conditional source information equals
--   $$\sum_{(s,\omega)} \Lambda(s,\omega)\; D\Big(P_B\big(\cdot \,\big|\, (i^\ast_s,\, y_{i^\ast_s}),\; \mathrm{hist}(s,\omega)\big)\,\Big\|\, \mu\big(\cdot \mid y_{i^\ast_s}\big)\Big),$$
--   summed over pairs of a seed $s$ (with distinguished coordinate $i^\ast_s$) and an outcome $\omega$, weighted by the postselected joint law $\Lambda$. Here $P_B$ is Bob's information posterior, viewed as a joint law on pairs (remaining coordinate, Bob's question, history flag) and Alice's question, and $\mu(\cdot \mid y) = \mu(\cdot, y)/\mu_Y(y)$ is the game's conditional distribution of Alice's question given Bob's.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L53896-L53949

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
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactBobSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × Y) ×
                  ExactHistoryFlag X Y A B D) × X =>
                exactBobInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalXGivenY
              (point.2.2.1 point.1.coordinate.val)) := by sorry
