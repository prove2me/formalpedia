-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
-- name    : CRCD_QuantumChannelContinuity_TensorOrder
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T03:12:04.729849+00:00
-- url     : https://prove2.me/theorems/509a32fc-0cf6-4166-b3c6-c1e6c086597d
-- title:
--   Complete-positive order and tensor-product algebra
-- statement:
--   For finite-dimensional complex Hilbert spaces, $\Phi\preceq_{\mathrm{CP}}\Phi'$ means $\Phi'-\Phi$ is completely positive. If $\Phi\preceq_{\mathrm{CP}}\Phi'$, $\Psi\preceq_{\mathrm{CP}}\Psi'$, and $\Phi,\Psi'$ are completely positive, then $\Phi\otimes\Psi\preceq_{\mathrm{CP}}\Phi'\otimes\Psi'$. The asymmetric endpoint premises follow the exact decomposition
--
--   $$
--   \Phi'\otimes\Psi'-\Phi\otimes\Psi=(\Phi'-\Phi)\otimes\Psi'+\Phi\otimes(\Psi'-\Psi).
--   $$
--
--   More generally, if $\Phi\preceq_{\mathrm{CP}}a\Phi'$, $\Psi\preceq_{\mathrm{CP}}b\Psi'$, $\Phi,\Psi'$ are CP, and $b\ge0$, then $\Phi\otimes\Psi\preceq_{\mathrm{CP}}ab(\Phi'\otimes\Psi')$; no separate sign premise on $a$ is imposed. Domination also survives tensoring with an identity. Identities are CP, nonnegative scalar multiples preserve CP, and tensor superoperators satisfy $(a\Phi)\otimes(b\Psi)=ab(\Phi\otimes\Psi)$ for arbitrary real $a,b$.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/TensorOrder.lean#L29-L113

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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
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
# Tensor preservation of complete-positive order

These are concrete tensor-superoperator statements for arbitrary finite-dimensional
spaces, not assumptions on an abstract tensor operation.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

/-- Nonnegative real scaling preserves complete positivity. -/
theorem cp_smul {Φ : T A B} (hΦ : IsCompletelyPositive Φ) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyPositive (c • Φ) := by
  apply (isCompletelyPositive_iff_cstarMatrix_nonneg _).mpr
  intro k X hX
  have hmap : X.map (c • Φ) = c • X.map Φ := by
    ext i j x
    simp [CStarMatrix.map_apply]
  rw [hmap]
  rw [← algebraMap_smul ℂ c (X.map Φ)]
  exact smul_nonneg (by exact_mod_cast hc : (0 : ℂ) ≤ (c : ℂ))
    ((isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hΦ k X hX)

/-- Exact bilinear identity for the difference of tensor superoperators. -/
theorem tensorSuperoperator_difference (Φ Φ' : T A B) (Ψ Ψ' : T C D) :
    tensorSuperoperator Φ' Ψ' - tensorSuperoperator Φ Ψ =
      tensorSuperoperator (Φ' - Φ) Ψ' + tensorSuperoperator Φ (Ψ' - Ψ) := by
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.sub_apply, LinearMap.add_apply, l_tensor_equiv_symm_tmul,
      tensorSuperoperator_apply]
    ext a c
    simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensor products preserve complete-positive domination. -/
theorem CPLe.tensor {Φ Φ' : T A B} {Ψ Ψ' : T C D}
    (hΦΦ' : CPLe Φ Φ') (hΨΨ' : CPLe Ψ Ψ')
    (hΦ : IsCompletelyPositive Φ) (hΨ' : IsCompletelyPositive Ψ') :
    CPLe (tensorSuperoperator Φ Ψ) (tensorSuperoperator Φ' Ψ') := by
  unfold CPLe
  rw [tensorSuperoperator_difference]
  exact cp_add (tensorSuperoperator_cp _ _ hΦΦ' hΨ')
    (tensorSuperoperator_cp _ _ hΦ hΨΨ')

/-- Scalar tensor factors multiply exactly. -/
theorem tensorSuperoperator_smul (Φ : T A B) (Ψ : T C D) (a b : ℝ) :
    tensorSuperoperator (a • Φ) (b • Ψ) = (a * b) • tensorSuperoperator Φ Ψ := by
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply, LinearMap.smul_apply]
    ext x y
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensoring two dominated CP maps multiplies their scalar domination constants. -/
theorem CPLe.tensor_scaled {Φ Φ' : T A B} {Ψ Ψ' : T C D} {a b : ℝ}
    (hΦΦ' : CPLe Φ (a • Φ')) (hΨΨ' : CPLe Ψ (b • Ψ'))
    (hΦ : IsCompletelyPositive Φ) (hΨ' : IsCompletelyPositive Ψ') (hb : 0 ≤ b) :
    CPLe (tensorSuperoperator Φ Ψ) ((a * b) • tensorSuperoperator Φ' Ψ') := by
  rw [← tensorSuperoperator_smul]
  exact hΦΦ'.tensor hΨΨ' hΦ (cp_smul hΨ' hb)

/-- The identity superoperator is completely positive. -/
theorem cp_identity : IsCompletelyPositive (LinearMap.id : T C C) := by
  have h := krausTerm_isCompletelyPositive (LinearMap.id : L C)
  have heq : krausTerm (LinearMap.id : L C) = (LinearMap.id : T C C) := by
    ext X x
    simp [krausTerm]
  rwa [heq] at h

/-- Domination survives an arbitrary finite entangled reference with the same
scalar constant. -/
theorem CPLe.tensor_identity_scaled {Φ Ψ : T A B} {a : ℝ}
    (h : CPLe Φ (a • Ψ)) (hΦ : IsCompletelyPositive Φ) :
    CPLe (tensorSuperoperator Φ (LinearMap.id : T C C))
      (a • tensorSuperoperator Ψ (LinearMap.id : T C C)) := by
  have hid : CPLe (LinearMap.id : T C C) LinearMap.id := by
    unfold CPLe
    rw [sub_self]
    simpa using cp_smul (cp_identity (C := C)) (c := 0) le_rfl
  have ht := h.tensor hid hΦ (cp_identity (C := C))
  have hscale : tensorSuperoperator (a • Ψ) (LinearMap.id : T C C) =
      a • tensorSuperoperator Ψ (LinearMap.id : T C C) := by
    simpa only [one_smul, mul_one] using
      tensorSuperoperator_smul Ψ (LinearMap.id : T C C) a 1
  rwa [hscale] at ht

end QuantumChannelContinuity


