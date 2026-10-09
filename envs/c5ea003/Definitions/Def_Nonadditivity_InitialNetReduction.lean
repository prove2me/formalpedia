-- Prove2me | Definitions.Def_Nonadditivity_InitialNetReduction
-- name    : Nonadditivity_InitialNetReduction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:53:09.196994+00:00
-- url     : https://prove2.me/theorems/ce22e8c9-c8f7-4e9f-a3db-5fdf085e69c5
-- title:
--   The coefficient polynomial of the initial finite test net
-- statement:
--   A finite family of test matrices defines a normalized block Gram matrix and square-root coefficient matrices on the product of branch and test indices. Collecting repeated branch words turns the construction into a finite-support polynomial. Its coefficient dimension is the product of the branch and test cardinalities, and its regular and finite evaluations agree with the explicitly assembled coefficient expressions. The interface also specifies the short word embeddings used in subsequent reduction steps.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/InitialNetReduction.lean#L31-L577

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





/-! # The undoubled initial Gram construction for a symmetric test net

The square coefficients have exactly `|B| * |J|` rows, and use only individual
branch words. The same coefficients are evaluated in finite representations
and on the actual infinite left regular Hilbert space.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Nonadditivity.InitialNetReduction
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder Kronecker
open FiniteSetFactorization (selector)
open RegularFactorization (term rectLift)

section Construction
variable {G B J : Type} [Group G] [DecidableEq G]
  [Fintype B] [DecidableEq B] [Nonempty B] [Fintype J] [DecidableEq J]

/-- The fixed, representation-independent positive coefficient matrix. -/
def gramMatrix (A : J → Matrix B B ℂ) : Matrix (B × J) (B × J) ℂ :=
  ((Fintype.card B : ℝ)⁻¹) • (1 + Matrix.blockDiagonal A)

/-- A single fixed column is sufficient; no Hermitian doubling occurs. -/
def coefficient (A : J → Matrix B B ℂ) (b₀ b : B) : Matrix (B × J) (B × J) ℂ :=
  CFC.sqrt (gramMatrix A) * (selector (ι := J) b).conjTranspose * selector b₀





def regularEval (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :=
  ∑ b, term (coefficient A b₀ b) (w b)
































section Finite
variable {V : Type*} [Fintype V] [DecidableEq V]



def finiteEval (U : B → unitary (Matrix V V ℂ)) (A : J → Matrix B B ℂ) (b₀ : B) :
    Matrix ((B × J) × V) ((B × J) × V) ℂ :=
  ∑ b, coefficient A b₀ b ⊗ₖ (U b : Matrix V V ℂ)

























end Finite

section Collection
variable [Nonempty J]

def collectedCoefficient (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) (g : G) :
    Matrix (B × J) (B × J) ℂ := ∑ b, if w b = g then coefficient A b₀ b else 0

/-- The actual polynomial record to which subsequent support reductions apply. -/
def polynomial (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    PolynomialReduction.Polynomial G where
  Index := B × J
  fintype := inferInstance
  decEq := inferInstance
  nonempty := inferInstance
  support := Finset.univ.image w
  coefficient := collectedCoefficient w A b₀

@[simp] theorem polynomial_dimension (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    Fintype.card (polynomial w A b₀).Index = Fintype.card B * Fintype.card J :=
  Fintype.card_prod _ _

@[simp] theorem polynomial_support (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    (polynomial w A b₀).support = Finset.univ.image w := rfl

 theorem collection_sum {E : Type*} [AddCommMonoid E]
    (w : B → G) (f : B → G → E) :
    ∑ g ∈ Finset.univ.image w, ∑ b, (if w b = g then f b g else 0) = ∑ b, f b (w b) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_ite_eq]
  simp

@[simp] theorem polynomial_regularEval (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B) :
    (polynomial w A b₀).regularEval = regularEval w A b₀ := by
  change RegularCoefficientEnergy.regularPolynomial _ _ = _
  rw [RegularFactorization.polynomial_eq]
  simp only [polynomial, collectedCoefficient]
  have ht (g : G) : term (∑ b, if w b = g then coefficient A b₀ b else 0) g =
      ∑ b, if w b = g then term (coefficient A b₀ b) g else 0 := by
    simp only [term, RegularFactorization.rectLift_sum, ContinuousLinearMap.finset_sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  simp_rw [ht]
  exact Nonadditivity.InitialNetReduction.collection_sum w (fun b g => term (coefficient A b₀ b) g)

@[simp] theorem polynomial_finiteEval {V : Type*} [Fintype V] [DecidableEq V]
    (w : B → G) (A : J → Matrix B B ℂ) (b₀ : B)
    (π : G →* unitary (Matrix V V ℂ)) :
    (polynomial w A b₀).finiteEval π = finiteEval (fun b => π (w b)) A b₀ := by
  ext x y
  change (∑ g ∈ Finset.univ.image w, collectedCoefficient w A b₀ g ⊗ₖ
    (π g : Matrix V V ℂ)) x y = (finiteEval (fun b => π (w b)) A b₀) x y
  rcases x with ⟨x,x'⟩
  rcases y with ⟨y,y'⟩
  simp only [finiteEval, Matrix.sum_apply, Matrix.kronecker_apply, collectedCoefficient,
    Finset.sum_mul, Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul]
  exact Nonadditivity.InitialNetReduction.collection_sum w (fun b g => coefficient A b₀ b x y * (π g : Matrix V V ℂ) x' y')




end Collection

end Construction

section Nets
open FreeModel FiniteRealization
variable {K n : ℕ}






end Nets


section ShortWords



/-- The actual logarithmic-length embedding with the target generators named
`Fin 2`, as required by the one-factor support and linear-polynomial APIs. -/
def shortEmbedding (K : ℕ) (hK : 2 ≤ K) : FreeGroup (Fin K) →* FreeGroup (Fin 2) :=
  (FreeGroup.freeGroupCongr finTwoEquiv.symm).toMonoidHom.comp (FreeEmbedding.logarithmicEmbedding K hK)



def shortWord (K : ℕ) (hK : 2 ≤ K) (a : Fin K) : FreeGroup (Fin 2) :=
  shortEmbedding K hK (FreeGroup.of a)



def shortProductEmbedding (K n : ℕ) (hK : 2 ≤ K) :
    FreeModel.ProductFreeGroup K n →* (Fin n → FreeGroup (Fin 2)) where
  toFun g i := shortEmbedding K hK (g i)
  map_one' := by ext i; exact map_one _
  map_mul' g h := by ext i; exact map_mul _ _ _



@[simp] theorem shortProductEmbedding_branchWord (K n : ℕ) (hK : 2 ≤ K)
    (a : FreeModel.Branch K n) :
    shortProductEmbedding K n hK (FreeModel.branchWord a) = fun i => shortWord K hK (a i) := rfl

end ShortWords

end Nonadditivity.InitialNetReduction


