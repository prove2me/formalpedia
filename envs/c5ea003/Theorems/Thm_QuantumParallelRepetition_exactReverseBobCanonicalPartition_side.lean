-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactReverseBobCanonicalPartition_side
-- name    : QuantumParallelRepetition.exactReverseBobCanonicalPartition_side
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-10T04:23:05.593527+00:00
-- url     : https://prove2.me/theorems/78300519-1908-45d2-a71c-0b65af58d059
-- title:
--   The canonical Bob colouring recovers its prescribed side
-- statement:
--   Let $M$ be a finite type with decidable equality, let $S \subseteq M$ contain a chosen coordinate $i$, and let $b$ be an arbitrary Boolean. Define the *canonical Bob colouring* by
--   $$\pi^{B}_{S,i,b}(j) = \begin{cases} b, & j = i,\\ \mathrm{true}, & j \neq i,\ j \in S,\\ \mathrm{false}, & j \neq i,\ j \notin S,\end{cases}$$
--   which is the canonical Alice colouring with the two colours interchanged. The theorem states that, for either value of $b$,
--   $$\{i\} \cup R\big(i, \pi^{B}_{S,i,b}\big) = S ,$$
--   where $R(i,\pi) = \{\, j \neq i : \pi(j) = \mathrm{true}\,\}$; that is, the reverse right side of the canonical Bob colouring is exactly the prescribed set $S$.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L31250-L31265

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

theorem QuantumParallelRepetition.exactReverseBobCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactRight coordinate
          (exactReverseBobCanonicalPartition
            side coordinate ignored)) = side := by sorry
