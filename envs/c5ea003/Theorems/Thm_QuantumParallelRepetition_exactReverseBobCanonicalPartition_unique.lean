-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobCanonicalPartition_unique
-- name    : QuantumParallelRepetition.exactReverseBobCanonicalPartition_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:28:02.816223+00:00
-- url     : https://prove2.me/theorems/0331fbad-5156-41f3-8af6-9bf007388ece
-- title:
--   Uniqueness of the colouring with a given reverse right side
-- statement:
--   Let $M$ be a finite type with decidable equality, fix $S \subseteq M$ and a coordinate $i$, and suppose $\pi : M \to \{\mathrm{false},\mathrm{true}\}$ is a colouring whose reverse right side is $S$, i.e. $\{i\} \cup R(i,\pi) = S$ with $R(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{true}\,\}$. Then
--   $$\pi = \pi^{B}_{S,\,i,\,\pi(i)} ,$$
--   the canonical Bob colouring determined by $S$, $i$ and the value of $\pi$ at $i$. With the companion lemma this exhibits the colourings having reverse right side $S$ as being exactly two in number, indexed by the value at the distinguished coordinate.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31267-L31289

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_19
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
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable

theorem QuantumParallelRepetition.exactReverseBobCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactRight coordinate partition) = side) :
    partition = exactReverseBobCanonicalPartition
      side coordinate (partition coordinate) := by sorry
