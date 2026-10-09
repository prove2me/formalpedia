-- Prove2me | Definitions.Def_Nonadditivity_StructuredFiniteChannel
-- name    : Nonadditivity_StructuredFiniteChannel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:55:23.534182+00:00
-- url     : https://prove2.me/theorems/618d9d3d-c911-427f-8e52-06065d23e034
-- title:
--   The block-channel adjoint as a branch polynomial
-- statement:
--   Let $K>0$, $n\ge0$, and let $U_{j,a}$ be finite-dimensional unitaries for tensor leg $j$ and branch letter $a\in\{0,\ldots,K-1\}$. For a branch tuple $a$, let $U_a$ be its ordered tensor word. If $A$ is a complex matrix indexed by the $K^n$ branch tuples, transport it to the block channel's output basis using the canonical branch/output equivalence. The genuine block-channel adjoint satisfies
--   $$T^*(A_{\mathrm{out}})=\frac1{K^n}\sum_{a,b}A_{ab}\,U_a^*U_b.$$
--   The bundle defines the coordinate transport and proves the exact identity, including the normalization, tensor order, and conjugate-transpose orientation. This identifies algebraic branch-polynomial evaluation with the finite Kraus channel used in the construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/StructuredFiniteChannel.lean#L27-L55

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounProduct
import Definitions.Def_Nonadditivity_CollinsYounTensor
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeEmbedding
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_InitialNetReduction
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_NetPolynomial
import Definitions.Def_Nonadditivity_NetPolynomialSupport
import Definitions.Def_Nonadditivity_ObservableDimension
import Definitions.Def_Nonadditivity_PolynomialDilation
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularFubini
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Star.Unitary

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # From the actual paired net polynomial to the actual block channel

The branch and standardized output indices are explicitly transported. A finite
polynomial norm bound therefore gives the concrete adjoint certificate used by
the entropy and channel-conversion theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

namespace Nonadditivity.StructuredFiniteChannel
open Entropy Channels Channels.KrausChannel FreeModel FreeBridge FiniteRealization
open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K n : ℕ} [NeZero K]

/-- An observable in branch coordinates, expressed in the output basis of the
concrete block channel. -/
def outputMatrix (A : Matrix (Branch K n) (Branch K n) ℂ) :
    Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ :=
  A.submatrix (branchToOutput K n).symm (branchToOutput K n).symm

@[simp] theorem branchToOutput_symm_output (a : TensorChainIndex (Fin K) n) :
    (branchToOutput K n).symm (BlockConstruction.blockOutputEquiv K n a) =
      chainBranchEquiv K n a := by
  apply (branchToOutput K n).injective
  simp

/-- The exact matrix identity, including the factor `1/K^n` and the orientation
`U_aᴴ U_b`, after conversion from nested tensor indices to branch tuples. -/
theorem block_adjoint_eq_branch_polynomial
    (U : ℕ → Fin K → unitary (Matrix ι ι ℂ))
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    (BlockConstruction.blockChannel U n).adjointMap (outputMatrix A) =
      ∑ a : Branch K n, ∑ b : Branch K n,
        ((Fintype.card (Branch K n) : ℂ)⁻¹ * A a b) •
          ((tensorWord U n ((chainBranchEquiv K n).symm a)).conjTranspose *
            tensorWord U n ((chainBranchEquiv K n).symm b)) := by
  rw [blockChannel_adjoint_eq_tensor_polynomial]
  simp only [Finset.smul_sum, smul_smul]
  apply Fintype.sum_equiv (chainBranchEquiv K n)
  intro a
  apply Fintype.sum_equiv (chainBranchEquiv K n)
  intro b
  simp [outputMatrix, Branch, one_div]

section Families
variable {J : Type} [Fintype J] [DecidableEq J]



end Families

section Certificates




end Certificates
end Nonadditivity.StructuredFiniteChannel


