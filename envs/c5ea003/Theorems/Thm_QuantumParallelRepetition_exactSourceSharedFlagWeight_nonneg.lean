-- Prove2me | Theorems.Thm_QuantumParallelRepetition_exactSourceSharedFlagWeight_nonneg
-- name    : QuantumParallelRepetition.exactSourceSharedFlagWeight_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-11T09:44:28.606308+00:00
-- url     : https://prove2.me/theorems/5ca9529f-0c4e-4ab3-a843-b4ca8d8df030
-- title:
--   The shared-flag weight is nonnegative
-- statement:
--   Fix $n$, a conditioned set $D\subseteq\{1,\dots,n\}$ and a denominator $q$. The shared randomness used by the exact source simulation ranges over pairs consisting of a coordinate outside $D$ and a permutation of the set of history flags paired with $\{1,\dots,q\}$, and every such pair carries the same weight $$w=\frac1{\#\{\text{coordinates outside }D\}}\cdot\frac1{\#\,\mathrm{Sym}\big(\mathcal F_D\times\{1,\dots,q\}\big)}.$$ The theorem states that this weight is nonnegative for every element of the shared-flag type.
-- source:
--   OpenAI, ten-proofs, QuantumParallelRepetition.lean, https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/QuantumParallelRepetition.lean#L46352-L46357

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_23
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Topology.Defs.Filter

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.exactSourceSharedFlagWeight_nonneg
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (j : ExactSourceSharedFlag X Y A B D denominator) :
    0 ≤ exactSourceSharedFlagWeight D denominator j := by sorry
