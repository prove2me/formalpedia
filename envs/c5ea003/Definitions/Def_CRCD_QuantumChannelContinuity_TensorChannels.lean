-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
-- name    : CRCD_QuantumChannelContinuity_TensorChannels
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:52:01.263387+00:00
-- url     : https://prove2.me/theorems/4581368b-3715-412d-be09-4b3e39812f62
-- title:
--   Tensor products of concrete quantum channels
-- statement:
--   For superoperators $\Phi:L(A)\to L(B)$ and $\Psi:L(C)\to L(D)$, transport their tensor product through the canonical finite-dimensional operator-tensor equivalence. The resulting map on $L(A\otimes C)$ satisfies
--   $$
--   (\Phi\otimes\Psi)(X\otimes Y)=\Phi(X)\otimes\Psi(Y).
--   $$
--   When both factors are completely positive and trace preserving, the construction bundles their tensor product as a completely positive trace-preserving channel. The complete positivity proof operates on every matrix amplification, and the trace proof extends the displayed pure-tensor rule by linearity.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorChannels.lean#L25-L104

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
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
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

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Tensor products and positive tensor powers of concrete channels

Complete positivity is proved using tensor products of Kraus operators;
trace preservation is extended from simple tensors by linearity.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

/-- The tensor product of two superoperators, transported through the
canonical finite-dimensional operator tensor equivalence. -/
noncomputable def tensorSuperoperator (Φ : T A B) (Ψ : T C D) :
    T (A ⊗[ℂ] C) (B ⊗[ℂ] D) :=
  (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := D)).symm.toLinearMap.comp
    ((TensorProduct.map Φ Ψ).comp (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).toLinearMap)

theorem tensorSuperoperator_apply (Φ : T A B) (Ψ : T C D) (X : L A) (Y : L C) :
    tensorSuperoperator Φ Ψ (TensorProduct.map X Y) = TensorProduct.map (Φ X) (Ψ Y) := by
  rw [← l_tensor_equiv_symm_tmul, ← l_tensor_equiv_symm_tmul]
  simp [tensorSuperoperator]

/-- Tensoring two Kraus operators tensors their conjugation maps. -/
theorem tensor_kraus_apply (V : A →ₗ[ℂ] B) (W : C →ₗ[ℂ] D) (X : L A) (Y : L C) :
    krausTerm (TensorProduct.map V W) (TensorProduct.map X Y) =
      TensorProduct.map (krausTerm V X) (krausTerm W Y) := by
  simp [krausTerm, TensorProduct.adjoint_map, ← TensorProduct.map_comp]

/-- The tensor product of actual completely positive superoperators is
completely positive, including every amplification. -/
theorem tensorSuperoperator_cp (Φ : T A B) (Ψ : T C D)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (tensorSuperoperator Φ Ψ) := by
  classical
  obtain ⟨ι, hi, fi, V, hV⟩ := cp_to_kraus (stdOrthonormalBasis ℂ A).toBasis Φ hΦ
  obtain ⟨κ, hk, fk, W, hW⟩ := cp_to_kraus (stdOrthonormalBasis ℂ C).toBasis Ψ hΨ
  letI := hi
  letI := fi
  letI := hk
  letI := fk
  have heq : tensorSuperoperator Φ Ψ =
      ∑ i : ι × κ, krausTerm (TensorProduct.map (V i.1) (W i.2)) := by
    apply LinearMap.ext
    intro Z
    obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul X Y =>
      rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply, hV, hW]
      rw [LinearMap.sum_apply, Fintype.sum_prod_type]
      simp only [tensor_kraus_apply]
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp [TensorProduct.sum_tmul, TensorProduct.tmul_sum, krausTerm]
        exact Finset.sum_comm
      | add x y hx hy => simp_all [map_add]
    | add x y hx hy => simp_all [Finset.sum_add_distrib]
  rw [heq]
  exact sum_krausTerm_isCompletelyPositive _

/-- Trace preservation of the tensor product. -/
theorem tensorSuperoperator_trace (Φ : CPTP A B) (Ψ : CPTP C D)
    (Z : L (A ⊗[ℂ] C)) :
    Tr (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap Z) = Tr Z := by
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct']
    change Tr (Φ.toFun X) * Tr (Ψ.toFun Y) = Tr X * Tr Y
    rw [← Φ.trace_map, ← Ψ.trace_map]
  | add x y hx hy => simp_all

/-- Tensor product of concrete CPTP quantum channels. -/
noncomputable def tensorChannel (Φ : CPTP A B) (Ψ : CPTP C D) :
    CPTP (A ⊗[ℂ] C) (B ⊗[ℂ] D) where
  toFun := tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap
  map_add' := (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap).map_add
  map_smul' := (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap).map_smul
  map_cstarMatrix_nonneg' k X hX := by
    obtain ⟨Γ, hΓ⟩ := tensorSuperoperator_cp Φ.toLinearMap Ψ.toLinearMap
      ⟨Φ.toCompletelyPositiveMap, rfl⟩ ⟨Ψ.toCompletelyPositiveMap, rfl⟩
    have h := Γ.map_cstarMatrix_nonneg' k X hX
    rw [hΓ] at h
    exact h
  trace_map X := (tensorSuperoperator_trace Φ Ψ X).symm

end QuantumChannelContinuity


