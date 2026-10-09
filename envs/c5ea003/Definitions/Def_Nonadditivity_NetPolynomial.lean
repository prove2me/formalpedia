-- Prove2me | Definitions.Def_Nonadditivity_NetPolynomial
-- name    : Nonadditivity_NetPolynomial
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:46:57.781801+00:00
-- url     : https://prove2.me/theorems/1d461674-4db8-4220-a24d-a7c35f9c6a77
-- title:
--   Direct sums of regular group-word test polynomials
-- statement:
--   A finite family of scalar group-word tests is represented by a diagonal matrix-coefficient polynomial on $\ell^2(G;\mathbb C^J)$. Coordinate slices and embeddings connect this vector-valued space with its scalar components, and diagonal coefficient evaluation acts by multiplying the corresponding scalar coordinate. The interface includes the scalar and regular polynomials and coordinate-permutation isometries used to transport these tests.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/NetPolynomial.lean#L29-L312

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
import Definitions.Def_Nonadditivity_ObservableDimension
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

namespace Nonadditivity.PrescribedTest
end Nonadditivity.PrescribedTest

namespace Nonadditivity.ShiftNorm
end Nonadditivity.ShiftNorm

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/






/-! # A finite family of observable tests as one actual polynomial

Diagonal coefficient matrices give a direct sum on the genuine vector-valued
regular Hilbert space. Its norm is the maximum of the scalar test norms.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Nonadditivity.NetPolynomial

open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator
open RegularCoefficientEnergy (CoefficientSpace)

section Slices
variable {G J : Type*} [Fintype J] [DecidableEq J]

/-- One scalar coordinate of a vector-valued square-summable function. -/
def slice (j : J) (f : RegularCoefficientEnergy.Hilbert G J) : FreeModel.Hilbert G :=
  ⟨fun g => f g j, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa using f.property.summable (by norm_num))
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun i _ => sq_nonneg ‖f g i‖) (Finset.mem_univ j)⟩

omit [DecidableEq J] in
@[simp] theorem slice_apply (j : J) (f : RegularCoefficientEnergy.Hilbert G J) (g : G) :
    slice j f g = f g j := rfl



/-- Include one scalar block isometrically in the coefficient direct sum. -/
def embed (j : J) (f : FreeModel.Hilbert G) : RegularCoefficientEnergy.Hilbert G J :=
  ⟨fun g => EuclideanSpace.single j (f g), by
    apply memℓp_gen
    simpa using f.property.summable (by norm_num)⟩

@[simp] theorem slice_embed (j k : J) (f : FreeModel.Hilbert G) :
    slice j (embed k f) = if j = k then f else 0 := by
  ext g
  by_cases h : j = k <;> simp [slice, embed, EuclideanSpace.single_apply, h]




end Slices

section Polynomial
variable {G J I : Type*} [Group G] [Fintype J] [DecidableEq J] [Fintype I]

/-- The diagonal coefficient `diag_j a_{ij}`. -/
def diagonalCoefficient (a : I → J → ℂ) (i : I) : Matrix J J ℂ :=
  Matrix.diagonal (a i)

/-- The literal matrix-coefficient regular polynomial on `ℓ²(G;ℂ^J)`. -/
def regularPolynomial (w : I → G) (a : I → J → ℂ) :
    RegularCoefficientEnergy.Hilbert G J →L[ℂ] RegularCoefficientEnergy.Hilbert G J :=
  MatrixRegularRestriction.coefficientPolynomial w
    (fun i => RegularCoefficientEnergy.coefficientOperator (diagonalCoefficient a i))

def scalarPolynomial (w : I → G) (a : I → J → ℂ) (j : J) :
    FreeModel.Hilbert G →L[ℂ] FreeModel.Hilbert G :=
  ∑ i, a i j • FreeModel.leftRegular (w i)

omit [Fintype I] in
@[simp] theorem diagonalCoefficient_apply (a : I → J → ℂ) (i : I)
    (x : CoefficientSpace J) (j : J) :
    RegularCoefficientEnergy.coefficientOperator (diagonalCoefficient a i) x j =
      a i j * x j := by
  change ((Matrix.diagonal (a i)) *ᵥ x.ofLp) j = _
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]








end Polynomial

section Tests
open FreeModel FiniteRealization
variable {K n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The coefficients in the manuscript, with the branch pair as term index. -/
def testCoefficient (A : J → Matrix (Branch K n) (Branch K n) ℂ)
    (p : Branch K n × Branch K n) (j : J) : ℂ := (1 / (K : ℂ)^n) * A j p.1 p.2

def testWord (p : Branch K n × Branch K n) : ProductFreeGroup K n :=
  (branchWord p.1)⁻¹ * branchWord p.2



omit [Fintype J] [DecidableEq J] in
@[simp] theorem scalar_testPolynomial
    (A : J → Matrix (Branch K n) (Branch K n) ℂ) (j : J) :
    scalarPolynomial testWord (testCoefficient A) j = gamma (A j) := by
  simp only [scalarPolynomial, testCoefficient, testWord, gamma, Fintype.sum_prod_type,
    Finset.smul_sum, mul_smul]






end Tests

section FiniteMatrices
variable {J V I : Type*} [Fintype J] [DecidableEq J]
  [Fintype V] [DecidableEq V] [Fintype I]
















end FiniteMatrices

section RegularSymmetry
variable {G J I : Type*} [Group G] [Fintype J] [DecidableEq J] [Fintype I]

/-- Reindex the finite coefficient coordinate inside the actual regular Hilbert space. -/
def permutationFunction (e : J ≃ J) (f : RegularCoefficientEnergy.Hilbert G J) :
    RegularCoefficientEnergy.Hilbert G J :=
  ⟨fun g => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm (f g), by
    apply memℓp_gen
    simpa only [LinearIsometryEquiv.norm_map] using f.property.summable (by norm_num)⟩

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationFunction_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    permutationFunction e f g j = f g (e j) := rfl

def permutationIsometry (e : J ≃ J) :
    RegularCoefficientEnergy.Hilbert G J ≃ₗᵢ[ℂ] RegularCoefficientEnergy.Hilbert G J where
  toFun := permutationFunction e
  invFun := permutationFunction e.symm
  left_inv := by intro f; ext g j; simp
  right_inv := by intro f; ext g j; simp
  map_add' := by intro f h; ext g j; rfl
  map_smul' := by intro z f; ext g j; rfl
  norm_map' := by
    intro f
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [MatrixRegularRestriction.norm_sq, MatrixRegularRestriction.norm_sq]
    exact tsum_congr (fun g => congrArg (fun x : ℝ => x^2)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map (f g)))

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationIsometry_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    permutationIsometry e f g j = f g (e j) := rfl

omit [Group G] [DecidableEq J] in
@[simp] theorem permutationIsometry_symm_apply (e : J ≃ J)
    (f : RegularCoefficientEnergy.Hilbert G J) (g : G) (j : J) :
    (permutationIsometry e).symm f g j = f g (e.symm j) := rfl




end RegularSymmetry

section RegularSelfAdjoint
variable {G J I : Type*} [Group G] [DecidableEq G] [Fintype J] [DecidableEq J] [Fintype I]




end RegularSelfAdjoint

section SelfAdjointTests
open FreeModel
variable {K n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]




end SelfAdjointTests

section ObservableNets
open FreeModel FiniteRealization
variable {K n : ℕ}




















end ObservableNets

end Nonadditivity.NetPolynomial


