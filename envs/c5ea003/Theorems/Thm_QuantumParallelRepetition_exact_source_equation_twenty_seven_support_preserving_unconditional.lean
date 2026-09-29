-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exact_source_equation_twenty_seven_support_preserving_unconditional
-- name    : QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving_unconditional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T15:59:14.351139+00:00
-- url     : https://prove2.me/theorems/22bf82bd-c50e-4c9f-8dcf-3dda07e0ab37
-- title:
--   Support-preserving sampler at the Pinsker rate, with no extra hypothesis
-- statement:
--   Same setting once more: positive postselected mass and at least one free coordinate. Then for every base history flag and every $\gamma > 0$, a support-preserving classical sampler exists with accuracy parameter equal to the Pinsker rate $\sqrt{R/2}$, where $R$ is the classical information rate. No information hypothesis is assumed; this is the unconditional form of the previous statement.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L57616-L57631

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
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
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem
    QuantumParallelRepetition.exact_source_equation_twenty_seven_support_preserving_unconditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by sorry
