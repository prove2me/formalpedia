-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseLeftSide_coordinate_mem
-- name    : QuantumParallelRepetition.exactReverseLeftSide_coordinate_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T02:54:04.592374+00:00
-- url     : https://prove2.me/theorems/b59f09a6-0dcc-480b-b5e3-40559d498665
-- title:
--   The distinguished coordinate belongs to the reverse left side
-- statement:
--   Let $M$ be a finite type with decidable equality and let $\sigma$ be a forward seed on $M$, consisting of a distinguished coordinate $i$, a two-colouring $\pi : M \to \{\mathrm{false},\mathrm{true}\}$, orderings of the two colour classes and cut points in them. Write
--   $$L(i,\pi) = \{\, j \in M : j \neq i,\ \pi(j) = \mathrm{false} \,\}$$
--   for the left block and $L^{+}(\sigma) = \{i\} \cup L(i,\pi)$ for the *reverse left side*, i.e. the left block together with the distinguished coordinate. The lemma records that $i \in L^{+}(\sigma)$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L28863-L28867

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

@[simp] theorem QuantumParallelRepetition.exactReverseLeftSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseLeftSide seed := by sorry
