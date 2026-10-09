-- Prove2me | Definitions.Def_Nonadditivity_NetPolynomialSupport
-- name    : Nonadditivity_NetPolynomialSupport
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:49:28.170684+00:00
-- url     : https://prove2.me/theorems/5759da94-c9d6-4335-8bd1-469f8e63a405
-- title:
--   Collection of repeated words into a finite-support polynomial
-- statement:
--   For finitely many indexed group words, take their image as the finite support and sum all scalar coefficients belonging to the same word. Place the resulting test coefficients on a diagonal matrix to obtain a polynomial with the original coefficient dimension. The finite sum identity shows that collecting repetitions preserves the evaluation, and the constructed regular polynomial equals the original direct sum of test polynomials on the same Hilbert space.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/NetPolynomialSupport.lean#L27-L76

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounProduct
import Definitions.Def_Nonadditivity_CollinsYounTensor
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
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_NetPolynomial
import Definitions.Def_Nonadditivity_ObservableDimension
import Definitions.Def_Nonadditivity_PolynomialDilation
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_PureChannelEntropy
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
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
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
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! # Collected-word polynomial for the observable test net

Repeated branch words are summed into actual matrix coefficients on a finite
support, so the constructed shortening theorem applies to the test polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Nonadditivity.NetPolynomialSupport
open scoped BigOperators Matrix Matrix.Norms.L2Operator Kronecker
open NetPolynomial

section Collection
variable {G J I : Type} [Group G] [DecidableEq G]
  [Fintype J] [DecidableEq J] [Fintype I]

def wordSupport (w : I → G) : Finset G := Finset.univ.image w

def collectedScalar (w : I → G) (a : I → J → ℂ) (g : G) (j : J) : ℂ :=
  ∑ i, if w i = g then a i j else 0

def collectedCoefficient (w : I → G) (a : I → J → ℂ) (g : G) : Matrix J J ℂ :=
  Matrix.diagonal (collectedScalar w a g)

omit [Group G] [Fintype J] [DecidableEq J] in
/-- Summing repeated words preserves every scalar finite evaluation. -/
theorem collected_sum {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (w : I → G) (a : I → J → ℂ) (j : J) (f : G → V) :
    ∑ g ∈ wordSupport w, collectedScalar w a g j • f g = ∑ i, a i j • f (w i) := by
  classical
  simp only [collectedScalar, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq]
  simp [wordSupport]

/-- The grouped coefficient polynomial is exactly the original direct sum,
on the same actual vector-valued Hilbert space. -/
theorem collected_regular_eq (w : I → G) (a : I → J → ℂ) :
    RegularCoefficientEnergy.regularPolynomial (wordSupport w) (collectedCoefficient w a) =
      NetPolynomial.regularPolynomial w a := by
  ext f g j
  simp only [RegularDilation.regularPolynomial_apply, WithLp.ofLp_sum, Finset.sum_apply,
    NetPolynomial.regularPolynomial, MatrixRegularRestriction.coefficientPolynomial_apply]
  have he (v : G) : RegularCoefficientEnergy.coefficientOperator (collectedCoefficient w a v)
      (f (v⁻¹*g)) j = collectedScalar w a v j * f (v⁻¹*g) j := by
    change (Matrix.diagonal (collectedScalar w a v) *ᵥ (f (v⁻¹*g)).ofLp) j = _
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  simp only [he, diagonalCoefficient_apply]
  exact collected_sum w a j (fun v => f (v⁻¹*g) j)

/-- A finite polynomial record with exactly the original coefficient dimension. -/
def polynomial [Nonempty J] (w : I → G) (a : I → J → ℂ) :
    PolynomialReduction.Polynomial G where
  Index := J
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := wordSupport w
  coefficient := collectedCoefficient w a

@[simp] theorem polynomial_regularEval [Nonempty J] (w : I → G) (a : I → J → ℂ) :
    (polynomial w a).regularEval = NetPolynomial.regularPolynomial w a :=
  collected_regular_eq w a




end Collection

end Nonadditivity.NetPolynomialSupport


