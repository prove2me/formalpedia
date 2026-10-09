-- Prove2me | Definitions.Def_Nonadditivity_FreeBridge
-- name    : Nonadditivity_FreeBridge
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:38:30.479772+00:00
-- url     : https://prove2.me/theorems/89944772-6538-4d4a-aa30-325944f1f318
-- title:
--   Coordinate identifications for tensor branches
-- statement:
--   For a type $\alpha$ and an integer $n\ge0$, identify the recursively nested tensor index $I_n(\alpha)$ with ordered tuples $\{0,\ldots,n-1\}\to\alpha$. For $K>0$, this induces the branch/output equivalence
--   $$I_n(\{0,\ldots,K-1\})\cong\{0,\ldots,K-1\}^{n}\cong\mathbb Z/(K^n\mathbb Z).$$
--   The ordering agrees with the concrete block channel: appending a tensor factor appends the last tuple coordinate. If $e:I\cong J$ is a bijection and $A$ is a complex matrix indexed by the finite set $J$, then reindexing both matrix coordinates preserves trace and Hilbert–Schmidt length:
--   $$\operatorname{Tr}(A[e,e])=\operatorname{Tr}A,\qquad\|A[e,e]\|_{\rm HS}=\|A\|_{\rm HS}.$$
--   These identifications connect free-group branch polynomials with the output basis used by the finite Kraus construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FreeBridge.lean#L29-L118

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/






/-!
# Exact observable-basis transport for the product free model

The nested block labels are canonically converted into ordered branch tuples.
Trace, Hermitian symmetry, and Hilbert--Schmidt length are preserved by the
actual matrix reindexing. Thus the Collins--Youn hypothesis supplies the
finite-net comparison bound after output coordinates have been specified.
-/

noncomputable section

namespace Nonadditivity.FreeBridge

open Nonadditivity.Entropy Nonadditivity.AdjointPurity
open scoped BigOperators Matrix

universe u

/-- The canonical ordered tuple associated with a recursively nested tensor label.
The last local tensor coordinate is the last coordinate of the finite tuple. -/
def chainTupleEquiv (α : Type u) : (n : ℕ) → TensorChainIndex α n ≃ (Fin n → α)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => PUnit.unit
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by funext i; exact Fin.elim0 i }
  | n + 1 =>
    { toFun := fun x => Fin.snoc (chainTupleEquiv α n x.1) x.2
      invFun := fun x => ((chainTupleEquiv α n).symm (Fin.init x), x (Fin.last n))
      left_inv := fun x => by rcases x with ⟨a,b⟩; simp
      right_inv := fun x => by simp [Fin.snoc_init_self] }

@[simp] theorem chainTupleEquiv_succ (α : Type u) (n : ℕ)
    (a : TensorChainIndex α n) (b : α) :
    chainTupleEquiv α (n + 1) (a,b) = Fin.snoc (chainTupleEquiv α n a) b := rfl

@[simp] theorem chainTupleEquiv_succ_symm (α : Type u) (n : ℕ) (a : Fin (n + 1) → α) :
    (chainTupleEquiv α (n + 1)).symm a =
      ((chainTupleEquiv α n).symm (Fin.init a), a (Fin.last n)) := rfl

def chainBranchEquiv (K n : ℕ) :
    TensorChainIndex (Fin K) n ≃ FreeModel.Branch K n := chainTupleEquiv (Fin K) n

section Reindex

variable {ι ο : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο]

omit [DecidableEq ι] [DecidableEq ο] in
/-- Trace is preserved by a bijective change of matrix basis labels. -/
theorem trace_submatrix_equiv (e : ι ≃ ο) (A : Matrix ο ο ℂ) :
    (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

omit [DecidableEq ι] [DecidableEq ο] in
/-- The matrix trace definition of Hilbert--Schmidt length is invariant under reindexing. -/
theorem hsLength_submatrix_equiv (e : ι ≃ ο) (A : Matrix ο ο ℂ) :
    hsLength (A.submatrix e e) = hsLength A := by
  unfold hsLength
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    trace_submatrix_equiv]



end Reindex

section Comparison

variable {K n : ℕ} {ο : Type*} [Fintype ο] [DecidableEq ο]







end Comparison

section Block

variable {K n : ℕ} [NeZero K]

/-- Ordered free-generator branches in the very output coordinates used by
`BlockConstruction.blockChannel`. The tuple conversion fixes the order of
the local tensor legs before applying the block's output basis equivalence. -/
def branchToOutput (K n : ℕ) [NeZero K] :
    FreeModel.Branch K n ≃ ZMod (K ^ n) :=
  (chainBranchEquiv K n).symm.trans (BlockConstruction.blockOutputEquiv K n)

@[simp] theorem branchToOutput_chain (a : TensorChainIndex (Fin K) n) :
    branchToOutput K n (chainBranchEquiv K n a) =
      BlockConstruction.blockOutputEquiv K n a := by
  simp [branchToOutput]















end Block

end Nonadditivity.FreeBridge


