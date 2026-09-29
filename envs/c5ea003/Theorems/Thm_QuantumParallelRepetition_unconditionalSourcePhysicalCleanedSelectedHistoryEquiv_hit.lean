-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
-- name    : QuantumParallelRepetition.unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T16:19:42.907019+00:00
-- url     : https://prove2.me/theorems/16156155-7fb9-4b44-ac70-055075ba85aa
-- title:
--   The selected component of a split history is the entry at the marked position
-- statement:
--   Let $L$ be a number of rounds, $j < L$ a marked round, and $\beta$ any type. The splitting equivalence that presents a history $f : \{0,1,\dots,L\} \to \beta$ as the triple (entry at the marked position, the $j$ entries strictly before it, the $L-j$ entries after it) returns $f(j)$ as its first component, where $j$ is viewed inside $\{0,\dots,L\}$ through the order-preserving inclusion. This is registered as a simp lemma so that the marked entry can be read off the split form automatically.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L61138-L61142

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_24
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

@[simp] theorem QuantumParallelRepetition.unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
    {L : ℕ} (j : Fin L) (β : Type*) (f : Fin (L + 1) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β f).1 = f j.castSucc := by sorry
