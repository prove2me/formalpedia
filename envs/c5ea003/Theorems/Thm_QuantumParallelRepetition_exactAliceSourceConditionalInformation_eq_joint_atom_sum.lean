-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactAliceSourceConditionalInformation_eq_joint_atom_sum
-- name    : QuantumParallelRepetition.exactAliceSourceConditionalInformation_eq_joint_atom_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T13:20:52.744506+00:00
-- url     : https://prove2.me/theorems/c97622fe-2551-4eb5-b3d0-f2c8635974ac
-- title:
--   Alice's conditional source information as a sum over postselected joint outcomes
-- statement:
--   Assume $|\bar D| > 0$ and that the postselection mass is positive, and fix a base history flag $r_0$. Then Alice's conditional source information equals
--   $$\sum_{(s,\omega)} \Lambda(s,\omega)\; D\Big(P_A\big(\cdot \,\big|\, (i^\ast_s,\, x_{i^\ast_s}),\; \mathrm{hist}(s,\omega)\big)\,\Big\|\, \mu\big(\cdot \mid x_{i^\ast_s}\big)\Big),$$
--   where the sum ranges over pairs consisting of a seed $s$ (with distinguished coordinate $i^\ast_s$) and an outcome $\omega$ of the repeated strategy, weighted by the postselected joint law $\Lambda$. Here $P_A$ is Alice's information posterior, regarded as a joint law on pairs (remaining coordinate, Alice's question, history flag) and Bob's question, its conditional is the induced distribution of Bob's question, $\mathrm{hist}(s,\omega)$ is the history flag coded by $(s,\omega)$, and $\mu(\cdot \mid x)$ is the game's conditional question distribution $\mu(x,\cdot)/\mu_X(x)$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L53841-L53894

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

theorem QuantumParallelRepetition.exactAliceSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                  ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalYGivenX
              (point.2.1 point.1.coordinate.val)) := by sorry
