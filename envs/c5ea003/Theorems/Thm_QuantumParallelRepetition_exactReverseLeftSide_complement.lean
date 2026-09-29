-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_complement
-- name    : QuantumParallelRepetition.exactReverseLeftSide_complement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:28:02.991926+00:00
-- url     : https://prove2.me/theorems/a0997ac8-d777-4fc7-bc5c-f4cf71ae808f
-- title:
--   The right block is the complement of the reverse left side
-- statement:
--   Let $M$ be a finite type with decidable equality and $\sigma$ a forward seed on $M$, with distinguished coordinate $i$ and two-colouring $\pi : M \to \{\mathrm{false},\mathrm{true}\}$. With $L(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{false}\,\}$, $R(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{true}\,\}$ and the reverse left side $L^{+}(\sigma) = \{i\} \cup L(i,\pi)$, the theorem states that
--   $$R(i,\pi) = M \setminus L^{+}(\sigma) .$$
--   Thus $M$ is partitioned into the reverse left side and the right block, and the right block is recoverable from the reverse left side alone. Together with the mirror statement this is what makes the reverse side a complete record of the colouring apart from its value at $i$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L30585-L30596

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.SetLike.Basic
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
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactReverseLeftSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRight seed.coordinate seed.partition =
      Finset.univ \ exactReverseLeftSide seed := by sorry
