-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_card
-- name    : QuantumParallelRepetition.exactReverseLeftSide_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T03:07:08.436554+00:00
-- url     : https://prove2.me/theorems/ff6b59e0-67f8-4b4d-bedd-bcf755aaa001
-- title:
--   Cardinality of the reverse left side
-- statement:
--   Let $\sigma$ be a forward seed on a finite type $M$ with decidable equality, with distinguished coordinate $i$ and two-colouring $\pi$, and let $L(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{false} \,\}$ be its left block and $L^{+}(\sigma) = \{i\} \cup L(i,\pi)$ its reverse left side. Then
--   $$|L^{+}(\sigma)| = |L(i,\pi)| + 1 .$$
--   The point is that the distinguished coordinate is genuinely new: it is excluded from the left block by definition, so adjoining it increases the cardinality by exactly one. This is what lets one index the reverse left side by $\mathrm{Fin}(|L(i,\pi)| + 1)$ when comparing the forward and reverse sampling procedures.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28875-L28881

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_17
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
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
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseLeftSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseLeftSide seed).card =
      (exactLeft seed.coordinate seed.partition).card + 1 := by sorry
