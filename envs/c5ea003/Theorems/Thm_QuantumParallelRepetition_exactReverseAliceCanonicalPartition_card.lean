-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseAliceCanonicalPartition_card
-- name    : QuantumParallelRepetition.exactReverseAliceCanonicalPartition_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:18:04.731313+00:00
-- url     : https://prove2.me/theorems/26b03e2a-b1e2-4001-865e-eee197795f86
-- title:
--   The left block of the canonical Alice partition has one element fewer than the side
-- statement:
--   Let $M$ be a finite type, $s\subseteq M$, $i\in s$ and $b\in\{0,1\}$, and let $\pi_{s,i,b}$ be the canonical Alice colouring, which sends $i$ to $b$, every other element of $s$ to $0$, and everything outside $s$ to $1$. Writing $L(i,\pi)=\{j\neq i:\pi(j)=0\}$, the theorem states the cardinality identity $$\big|L\big(i,\pi_{s,i,b}\big)\big|+1=|s| .$$ It records that removing the marked coordinate from $s$ leaves exactly the left block, which is the arithmetic fact needed to transport ranks of $s$ to ranks of $L\cup\{i\}$ when decoding a seed.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L33208-L33218

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_18
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseAliceCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactLeft coordinate
      (exactReverseAliceCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by sorry
