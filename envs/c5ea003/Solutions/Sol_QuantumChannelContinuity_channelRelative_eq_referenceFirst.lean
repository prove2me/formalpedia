-- Prove2me | solution 1 for QuantumChannelContinuity.channelRelative_eq_referenceFirst
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:00:54.571799+00:00
-- url     : https://prove2.me/submissions/c96858b8-f13a-42a2-80ac-dd8f390d8fa2

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_Quantum_QuantumEntropy_CFCDeriv
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_5
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiUmegaki_part_2
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean
import Definitions.Def_CRCD_QuantumChannelContinuity_ChannelTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Regularization
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_SourceCorrespondence
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorDilation
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorRegrouping
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorWords

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Correspondence with the manuscript's tensor-factor convention

The manuscript writes stabilized outputs as `(id ⊗ N)(|ψ⟩⟨ψ|)`, with the
reference first. The implementation's `amplifiedOutput` acts on the first
factor. Tensor swaps identify the two output states and their optimized
support-aware divergences at every admissible Rényi order.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B]

/-- Conjugating by the tensor swap exchanges tensor-product operators. -/
private theorem isoConj_comm_tensor (X : L A) (Y : L B) :
    isoConj (TensorProduct.commIsometry ℂ A B) (TensorProduct.map X Y) =
      TensorProduct.map Y X := by
  change (TensorProduct.commIsometry ℂ A B).toLinearMap.comp
    ((TensorProduct.map X Y).comp
      (LinearMap.adjoint (TensorProduct.commIsometry ℂ A B).toLinearMap)) = _
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
  ext a b
  simp

/-- The tensor swap intertwines the actual reference-first superoperator with
`amplifyWithId` on every input operator. -/
private theorem tensorSuperoperator_id_swap (N : CPTP A B) (X : L (A ⊗[ℂ] A)) :
    tensorSuperoperator (LinearMap.id : T A A) N.toLinearMap
      (isoConj (TensorProduct.commIsometry ℂ A A) X) =
    isoConj (TensorProduct.commIsometry ℂ B A) (amplifyWithId N.toLinearMap X) := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := A)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, isoConj_comm_tensor, tensorSuperoperator_apply,
      amplifyWithId_tensor, isoConj_comm_tensor]
    rfl
  | add x y hx hy => simp_all

variable [Nontrivial A] [Nontrivial B]



/-- Swapping input and output factors intertwines the two actual channel actions
on arbitrary density operators, including entangled inputs. -/
private theorem referenceFirstOutput_swap (N : CPTP A B)
    (ρ : DensityState (A ⊗[ℂ] A)) :
    referenceFirstOutput N
      (ρ.map (isometryChannel (TensorProduct.commIsometry ℂ A A))) =
    (amplifiedOutput N ρ).map
      (isometryChannel (TensorProduct.commIsometry ℂ B A)) := by
  apply DensityState.ext
  exact tensorSuperoperator_id_swap N ρ.op





end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A B : Type} [Qudit A] [Qudit B]
variable [Nontrivial A] [Nontrivial B]
open QuantumChannelContinuity in
/-- Relative entropy has the same exact correspondence of pure-input suprema,
including support-mismatch infinities. -/
theorem solution (N M : CPTP A B) :
    channelRelative N M =
      ⨆ ψ : PureInput (A ⊗[ℂ] A),
        (stateRelative (referenceFirstOutput N ψ.density)
          (referenceFirstOutput M ψ.density)).toENNReal := by
  rw [← (pureInputEquiv (TensorProduct.commIsometry ℂ A A)).iSup_comp]
  apply iSup_congr
  intro ψ
  change (stateRelative (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density)).toENNReal =
      (stateRelative (referenceFirstOutput N (ψ.mapIso
        (TensorProduct.commIsometry ℂ A A)).density)
        (referenceFirstOutput M (ψ.mapIso
          (TensorProduct.commIsometry ℂ A A)).density)).toENNReal
  rw [PureInput.density_mapIso, referenceFirstOutput_swap, referenceFirstOutput_swap,
    stateRelative_isometry]

end
