-- Prove2me | Definitions.Def_Nonadditivity_FiniteBlockModel
-- name    : Nonadditivity_FiniteBlockModel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T21:03:06.297119+00:00
-- url     : https://prove2.me/theorems/9b3b1531-4569-43cf-968e-c6553afab68d
-- title:
--   Concrete finite block channels with exact even-moment bounds
-- statement:
--   Fix integers $K\ge2$, $n\ge1$, and $p\ge0$. Complete free-generator translations on the radius-$4p$ word ball to a finite permutation group, take its finite regular unitary representation, and tensor $n$ copies. This yields concrete unitaries for a genuine block Kraus channel $T$ with finite input index $I$ and output dimension $K^n$. For every traceless output matrix $A$,
--   $$\operatorname{Re}\operatorname{Tr}((T^*(A))^{2p})\le |I|\,(c_{K,n}\|A\|_{\rm HS})^{2p},\qquad c_{K,n}=\sqrt{\frac{(1+9/K)^n-1}{K^n}}.$$
--   If $\|A\|_{\rm HS}\le1$, the normalized moment is at most $c_{K,n}^{2p}$. The bundle proves the exact bounded-word regular trace identities, their tensorization, and the equality of finite group-polynomial evaluation with the block adjoint. These exact finite models supply the moment premise required by deterministic spectral damping.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FiniteBlockModel.lean#L29-L205

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
import Definitions.Def_Nonadditivity_FiniteFreeModel
import Definitions.Def_Nonadditivity_FiniteMomentMatching
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FiniteRegularMatrix
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
import Definitions.Def_Nonadditivity_StructuredFiniteChannel
import Definitions.Def_Nonadditivity_StructuredHaarModel
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
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
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
import Mathlib.Data.Fintype.Vector
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
import Mathlib.GroupTheory.GroupAction.Basic
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







/-! # Exact finite block-channel moments

Finite quotients separating bounded free words give actual finite tensor
unitaries. Their block-channel trace moments agree exactly with the free trace.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace Nonadditivity.FiniteBlockModel
open Entropy Channels.KrausChannel FreeModel FreeBridge FiniteRealization
open scoped Matrix Matrix.Norms.L2Operator Kronecker BigOperators
open StructuredHaarModel (kroneckerUnitary)

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : ℕ}

/-- A literal product-free-group representation on the tensor input space. -/
def tensorRepresentation (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ))) :
    (r : ℕ) → (Fin r → FreeGroup (Fin K)) →*
      unitary (Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ)
  | 0 => 1
  | r+1 =>
    { toFun := fun g => kroneckerUnitary (tensorRepresentation u r (Fin.init g)) (u r (g (Fin.last r)))
      map_one' := by
        apply Subtype.ext
        change (tensorRepresentation u r (Fin.init (1 : Fin (r+1) → FreeGroup (Fin K))) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
          (u r 1 : Matrix ι ι ℂ) = 1
        have hi : Fin.init (1 : Fin (r+1) → FreeGroup (Fin K)) = 1 := rfl
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
theorem tensorRepresentation_word
    (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ)))
    (w : ℕ → Fin K → FreeGroup (Fin K)) (r : ℕ) (a : FreeModel.Branch K r) :
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

/-- The normalized regular character tensorizes exactly. -/
theorem tensorRepresentation_trace
    (u : ℕ → (FreeGroup (Fin K) →* unitary (Matrix ι ι ℂ))) (R : ℕ)
    (hu : ∀ j w, FreeGroup.norm w ≤ R →
      (u j w : Matrix ι ι ℂ).trace = (Fintype.card ι : ℂ)*(if w=1 then 1 else 0))
    (r : ℕ) (w : Fin r → FreeGroup (Fin K)) (hw : ∀ j, FreeGroup.norm (w j) ≤ R) :
    (tensorRepresentation u r w : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ).trace =
      (Fintype.card (TensorChainIndex ι r):ℂ)*(if w=1 then 1 else 0) := by
  induction r with
  | zero =>
    have he : w=1 := by funext i; exact Fin.elim0 i
    simp [tensorRepresentation,he]
  | succ r ih =>
    change ((tensorRepresentation u r (Fin.init w) : Matrix (TensorChainIndex ι r) (TensorChainIndex ι r) ℂ) ⊗ₖ
      (u r (w (Fin.last r)) : Matrix ι ι ℂ)).trace = _
    rw [Matrix.trace_kronecker,ih (Fin.init w) (fun j => hw j.castSucc),
      hu r (w (Fin.last r)) (hw (Fin.last r))]
    have he : w=1 ↔ Fin.init w=1 ∧ w (Fin.last r)=1 := by
      constructor
      · rintro rfl; exact ⟨rfl,rfl⟩
      · rintro ⟨ha,hb⟩
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · exact hb
        · exact congrFun ha i
    by_cases ha : Fin.init w=1 <;> by_cases hb : w (Fin.last r)=1 <;>
      simp [he,ha,hb,TensorChainIndex,Fintype.card_prod]

end Tensor

section FiniteModel

/-- The finite group of completed translations on the word ball. -/
abbrev LocalIndex (K R : ℕ) := Equiv.Perm (FiniteFreeModel.Ball (Fin K) R)

/-- Genuine local unitary evaluation with exactly regular trace through radius R. -/
def localRepresentation (K R : ℕ) :
    FreeGroup (Fin K) →* unitary (Matrix (LocalIndex K R) (LocalIndex K R) ℂ) :=
  (FiniteRegularMatrix.regularUnitary (LocalIndex K R)).comp (FiniteFreeModel.model R)

theorem localRepresentation_trace (K R : ℕ) (w : FreeGroup (Fin K))
    (hw : FreeGroup.norm w ≤ R) :
    (localRepresentation K R w : Matrix (LocalIndex K R) (LocalIndex K R) ℂ).trace =
      (Fintype.card (LocalIndex K R):ℂ)*(if w=1 then 1 else 0) := by
  change (FiniteRegularMatrix.regularUnitary (LocalIndex K R) (FiniteFreeModel.model R w) :
    Matrix (LocalIndex K R) (LocalIndex K R) ℂ).trace = _
  rw [FiniteRegularMatrix.regularUnitaryHom_trace]
  simp only [FiniteFreeModel.model_eq_one_iff R w hw]

/-- The concrete local unitaries supplied to the existing block-channel constructor. -/
def baseUnitary (K R : ℕ) (_j : ℕ) (a : Fin K) :
    unitary (Matrix (LocalIndex K R) (LocalIndex K R) ℂ) :=
  localRepresentation K R (FreeGroup.of a)

/-- The concrete tensor representation, with matrix codomain for algebraic moments. -/
def representation (K R n : ℕ) : ProductFreeGroup K n →*
    Matrix (TensorChainIndex (LocalIndex K R) n) (TensorChainIndex (LocalIndex K R) n) ℂ where
  toFun w := tensorRepresentation (fun _ => localRepresentation K R) n w
  map_one' := congrArg Subtype.val (map_one (tensorRepresentation (fun _ => localRepresentation K R) n))
  map_mul' v w := congrArg Subtype.val (map_mul (tensorRepresentation (fun _ => localRepresentation K R) n) v w)

theorem representation_trace (K R n : ℕ) (w : ProductFreeGroup K n)
    (hw : ∀j, FreeGroup.norm (w j) ≤ R) :
    (representation K R n w).trace =
      (Fintype.card (TensorChainIndex (LocalIndex K R) n):ℂ)*(if w=1 then 1 else 0) :=
  tensorRepresentation_trace (fun _ => localRepresentation K R) R
    (fun _ => localRepresentation_trace K R) n w hw

theorem representation_branchWord (K R n : ℕ) (a : Branch K n) :
    representation K R n (branchWord a) =
      tensorWord (baseUnitary K R) n ((chainBranchEquiv K n).symm a) :=
  tensorRepresentation_word (fun _ => localRepresentation K R)
    (fun _ => FreeGroup.of) n a

theorem representation_inv (K R n : ℕ) (w : ProductFreeGroup K n) :
    representation K R n w⁻¹ = (representation K R n w).conjTranspose := by
  change ((tensorRepresentation (fun _ => localRepresentation K R) n w⁻¹) :
    Matrix (TensorChainIndex (LocalIndex K R) n) (TensorChainIndex (LocalIndex K R) n) ℂ) = _
  rw [map_inv]
  rfl

/-- The algebraic finite polynomial is exactly the actual block adjoint. -/
theorem finiteEval_eq_block_adjoint (K R n : ℕ) [NeZero K]
    (A : Matrix (Branch K n) (Branch K n) ℂ) :
    FiniteMomentMatching.finiteEval (representation K R n) (FiniteMomentMatching.gammaPolynomial A) =
      (BlockConstruction.blockChannel (baseUnitary K R) n).adjointMap
        (StructuredFiniteChannel.outputMatrix A) := by
  rw [FiniteMomentMatching.finiteEval_gammaPolynomial,
    StructuredFiniteChannel.block_adjoint_eq_branch_polynomial]
  simp only [Finset.smul_sum,smul_smul,map_mul,representation_inv,representation_branchWord]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [Branch,one_div]

/-- Exact finite moments for every observable, with the genuine HS factor. -/
theorem block_adjoint_moment_le {K n : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hn : 1 ≤ n) (p : ℕ)
    (A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ) (hA : A.trace=0) :
    (((BlockConstruction.blockChannel (baseUnitary K (4*p)) n).adjointMap A)^(2*p)).trace.re ≤
      (Fintype.card (TensorChainIndex (LocalIndex K (4*p)) n):ℝ)*
        (c K n*AdjointPurity.hsLength A)^(2*p) := by
  let B := A.submatrix (branchToOutput K n) (branchToOutput K n)
  have ht : B.trace=0 := (trace_submatrix_equiv _ A).trans hA
  have hb := FiniteMomentMatching.gamma_trace_pow_re_le hK hn
    (representation K (4*p) n) B ht (2*p) (fun w hw =>
      representation_trace K (4*p) n w (by simpa only [←Nat.mul_assoc] using hw))
  rw [finiteEval_eq_block_adjoint] at hb
  have he : StructuredFiniteChannel.outputMatrix B = A := by
    ext a b
    simp [StructuredFiniteChannel.outputMatrix,B]
  rw [he] at hb
  simpa only [B,hsLength_submatrix_equiv] using hb

/-- Normalized even moments of every traceless HS-unit-ball test are at most c^(2p).
All matrices here belong to an explicitly constructed genuine block channel. -/
theorem block_adjoint_normalized_moment_le {K n : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hn : 1 ≤ n) (p : ℕ)
    (A : Matrix (ZMod (K^n)) (ZMod (K^n)) ℂ) (hA : A.trace=0)
    (hhs : AdjointPurity.hsLength A ≤ 1) :
    (((BlockConstruction.blockChannel (baseUnitary K (4*p)) n).adjointMap A)^(2*p)).trace.re /
      (Fintype.card (TensorChainIndex (LocalIndex K (4*p)) n):ℝ) ≤ (c K n)^(2*p) := by
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos)).mpr
  apply (block_adjoint_moment_le hK hn p A hA).trans
  rw [mul_comm ((c K n)^(2*p))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by unfold c AdjointPurity.hsLength; positivity)
  exact (mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg _)).trans_eq (mul_one _)

end FiniteModel

end Nonadditivity.FiniteBlockModel


