-- Prove2me | Definitions.Def_Nonadditivity_TensorPartitionReduction
-- name    : Nonadditivity_TensorPartitionReduction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:47:32.794986+00:00
-- url     : https://prove2.me/theorems/d6f5cc7e-5124-4785-8eee-120b56e9eb29
-- title:
--   Finite supports from balanced tensor-coordinate partitions
-- statement:
--   At level $j$, residue classes modulo $2^j$ partition the $n$ tensor coordinates. The width is the integer ceiling of $n/2^j$, and each coordinate's quotient index lies below that width. A coded word assigns local generator choices to one residue class. The finite stage support consists of all such coded words and their inverses, together with the identity; the identity membership is supplied for the reduction construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/TensorPartitionReduction.lean#L26-L77

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Constructed balanced tensor-coordinate factorization

Residue classes modulo `2^j` form a balanced partition of the coordinates.
Each class splits into two at the next level.  The constructed supports
include both signs and have the manuscript's `1 + 2^(j+1) K^ceil(n/2^j)` bound.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Nonadditivity.TensorPartitionReduction
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open PolynomialReduction ProductPolynomialReduction

variable {α : Type} [DecidableEq α] {n K : ℕ} [NeZero K]

/-- Integer ceiling of the number of coordinates per residue class. -/
def width (n j : ℕ) : ℕ := (n + 2^j - 1) / 2^j

theorem quotient_lt_width (i : Fin n) (j : ℕ) : i.val / 2^j < width n j := by
  have hp : 0 < 2^j := by positivity
  unfold width
  have hi := Nat.mul_div_le i.val (2^j)
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le hp).mpr
  have hsub : n + 2^j - 1 + 1 = n + 2^j := Nat.sub_add_cancel (by omega)
  nlinarith [i.isLt]



/-- An equivalent coding using only `ceil(n/2^j)` local choices. -/
def codedWord (v : Fin n → Fin K → FreeGroup α) (j : ℕ)
    (c : Fin (2^j) × (Fin (width n j) → Fin K)) : GroupWord α n :=
  fun i => if i.val % 2^j = c.1.val then
    v i (c.2 ⟨i.val / 2^j, quotient_lt_width i j⟩) else 1





/-- The actual finite support at partition level `j`. -/
def stageSupport (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    Finset (GroupWord α n) :=
  insert 1 ((Finset.univ.image (codedWord v j)) ∪
    Finset.univ.image (fun c => (codedWord v j c)⁻¹))

@[simp] theorem one_mem_stageSupport (v : Fin n → Fin K → FreeGroup α) (j : ℕ) :
    (1 : GroupWord α n) ∈ stageSupport v j := by simp [stageSupport]






























































end Nonadditivity.TensorPartitionReduction


