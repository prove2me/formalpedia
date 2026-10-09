-- Prove2me | Definitions.Def_Nonadditivity_StructuredHaarModel
-- name    : Nonadditivity_StructuredHaarModel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T21:00:33.73998+00:00
-- url     : https://prove2.me/theorems/8122fbf9-0fd9-40cc-b7b3-dd77531ff993
-- title:
--   Tensor representations obtained from sampled unitary pairs
-- statement:
--   Let $\omega$ contain two Haar-sampled $(N+1)$-dimensional unitaries for each of $n$ tensor legs. Evaluating free words in each sampled pair defines $\rho_{j,\omega}:F_2\to U(N+1)$. Their literal tensor representation is
--   $$\rho_\omega(g_0,\ldots,g_{n-1})=\bigotimes_{j=0}^{n-1}\rho_{j,\omega}(g_j).$$
--   For $K\ge2$, let $w_a\in F_2$ be the generator word supplied by the source's logarithmic-embedding construction for branch letter $a\in\{0,\ldots,K-1\}$. Define derived unitaries $V_{j,a}=\rho_{j,\omega}(w_a)$. The bundle proves that evaluating an embedded branch tuple gives exactly its ordered tensor word $\bigotimes_j V_{j,a_j}$, including the conversion to the concrete tensor-chain basis.
--   It also constructs Kronecker products as genuine unitaries. All derived unitaries within a leg are formed from that leg's sampled pair; the definitions specify the joint model through this common pair.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/StructuredHaarModel.lean#L27-L116

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
import Definitions.Def_Nonadditivity_StructuredLinearization
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPartitionReduction
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Definitions.Def_Nonadditivity_WordBallReduction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
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





/-! # Concrete tensor representation of independent Haar generator pairs

The explicit construction samples two independent Haar matrices per tensor
factor, then evaluates the proved logarithmic-length words. The derived K
unitaries within each factor are not asserted independent or Haar.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
namespace Nonadditivity.StructuredHaarModel
open MeasureTheory Entropy Channels.KrausChannel
open scoped Matrix Matrix.Norms.L2Operator Kronecker BigOperators Topology

section Tensor
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def kroneckerUnitary (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ)) :
    unitary (Matrix (ι×κ) (ι×κ) ℂ) :=
  ⟨(U:Matrix ι ι ℂ) ⊗ₖ (V:Matrix κ κ ℂ), by
    apply Unitary.mem_iff.mpr
    constructor
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker]
      rw [← Matrix.mul_kronecker_mul]
      change (star (U:Matrix ι ι ℂ)*(U:Matrix ι ι ℂ)) ⊗ₖ
        (star (V:Matrix κ κ ℂ)*(V:Matrix κ κ ℂ)) = 1
      rw [(Unitary.mem_iff.mp U.property).1,(Unitary.mem_iff.mp V.property).1,
        Matrix.one_kronecker_one]
    · simp only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_kronecker]
      rw [← Matrix.mul_kronecker_mul]
      change ((U:Matrix ι ι ℂ)*star (U:Matrix ι ι ℂ)) ⊗ₖ
        ((V:Matrix κ κ ℂ)*star (V:Matrix κ κ ℂ)) = 1
      rw [(Unitary.mem_iff.mp U.property).2,(Unitary.mem_iff.mp V.property).2,
        Matrix.one_kronecker_one]⟩

/-- A literal product-free-group representation on the tensor input space. -/
def tensorRepresentation (u : ℕ → (FreeGroup (Fin 2) →* unitary (Matrix ι ι ℂ))) :
    (r : ℕ) → (Fin r → FreeGroup (Fin 2)) →*
      unitary (Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)
  | 0 => 1
  | r+1 =>
    { toFun := fun g => kroneckerUnitary (tensorRepresentation u r (Fin.init g)) (u r (g (Fin.last r)))
      map_one' := by
        apply Subtype.ext
        change (tensorRepresentation u r (Fin.init (1 : Fin (r+1) → FreeGroup (Fin 2))) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r 1 : Matrix ι ι ℂ) = 1
        have hi : Fin.init (1 : Fin (r+1) → FreeGroup (Fin 2)) = 1 := rfl
        rw [hi,map_one,map_one]
        exact Matrix.one_kronecker_one
      map_mul' := by
        intro g h
        apply Subtype.ext
        have hi : Fin.init (g*h) = Fin.init g * Fin.init h := rfl
        change (tensorRepresentation u r (Fin.init (g*h)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r ((g*h) (Fin.last r)) : Matrix ι ι ℂ) = _
        rw [hi,map_mul]
        change ((tensorRepresentation u r (Fin.init g) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) *
          (tensorRepresentation u r (Fin.init h) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)) ⊗ₖ
          (u r (g (Fin.last r)*h (Fin.last r)) : Matrix ι ι ℂ) = _
        rw [map_mul]
        exact Matrix.mul_kronecker_mul _ _ _ _ }

/-- The representation evaluates individual branch words to the actual ordered
tensor words used by the Kraus-channel construction. -/
theorem tensorRepresentation_word {K : ℕ}
    (u : ℕ → (FreeGroup (Fin 2) →* unitary (Matrix ι ι ℂ)))
    (w : ℕ → Fin K → FreeGroup (Fin 2)) (r : ℕ) (a : FreeModel.Branch K r) :
    (tensorRepresentation u r (fun i => w i.val (a i)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) =
      tensorWord (fun j b => u j (w j b)) r ((FreeBridge.chainBranchEquiv K r).symm a) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (tensorRepresentation u r (fun i => w i.val (a i.castSucc)) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ) = _
    change (tensorRepresentation u r (fun i => w i.val (a i.castSucc)) :
      Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ) =
      tensorWord (fun j b => u j (w j b)) r
        ((FreeBridge.chainBranchEquiv K r).symm (Fin.init a)) ⊗ₖ
      (u r (w r (a (Fin.last r))) : Matrix ι ι ℂ)
    congr 1
    simpa only [Fin.init] using ih (Fin.init a)
end Tensor

/-- Local free-group evaluation in each independently sampled Haar pair. -/
def localRepresentation (n N : ℕ) (ω : HaarModel.Sample 2 n N) (j : ℕ) :
    FreeGroup (Fin 2) →* HaarModel.LocalUnitary N :=
  FreeGroup.lift (HaarModel.sampleUnitary 2 n N ω j)

/-- The canonical tensor representation of all sampled pairs. -/
def sampleRepresentation (n N : ℕ) (ω : HaarModel.Sample 2 n N) :
    StructuredLinearization.G n →*
      unitary (Matrix (TensorChainIndex (Fin (N+1)) n) (TensorChainIndex (Fin (N+1)) n) ℂ) :=
  tensorRepresentation (localRepresentation n N ω) n

/-- The actual K derived unitaries, obtained from the logarithmic-length embedding. -/
def derivedUnitary (K n N : ℕ) (hK : 2 ≤ K) (ω : HaarModel.Sample 2 n N)
    (j : ℕ) (a : Fin K) : HaarModel.LocalUnitary N :=
  localRepresentation n N ω j (InitialNetReduction.shortWord K hK a)

@[simp] theorem sampleRepresentation_branchWord (K n N : ℕ) (hK : 2 ≤ K)
    (ω : HaarModel.Sample 2 n N) (a : FreeModel.Branch K n) :
    (sampleRepresentation n N ω
      (InitialNetReduction.shortProductEmbedding K n hK (FreeModel.branchWord a)) : Matrix _ _ ℂ) =
      tensorWord (derivedUnitary K n N hK ω) n ((FreeBridge.chainBranchEquiv K n).symm a) :=
  tensorRepresentation_word (localRepresentation n N ω)
    (fun _ => InitialNetReduction.shortWord K hK) n a









end Nonadditivity.StructuredHaarModel


