-- Prove2me | Definitions.Def_CRCD_QuantumChannelContinuity_SDPTrace
-- name    : CRCD_QuantumChannelContinuity_SDPTrace
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T02:43:15.062031+00:00
-- url     : https://prove2.me/theorems/4fb15620-f32d-4cd9-9f99-2e727248d76f
-- title:
--   Hermitian operators and real trace duality
-- statement:
--   The Hermitian operators on a finite-dimensional complex Hilbert space form a real vector space. Define the real trace functional and trace pairing by
--   $$
--   \tau(X)=\operatorname{Re}\operatorname{Tr}X,\qquad \langle X,Y\rangle_{\operatorname{Tr}}=\operatorname{Re}\operatorname{Tr}(XY).
--   $$
--   The pairing identifies this space with its real algebraic dual in finite dimension. Positivity is characterized by nonnegative pairing with every positive Hermitian operator. The associated order and norm estimates include $\|X\|\le\tau(X)$ for positive $X$, and monotonicity of the trace under the Hermitian order.
-- source:
--   https://github.com/JWang226/Continuity-of-regularized-channel-renyi-divergence/blob/e29274a69978bb499f00497481c6008befb0b84d/QuantumChannelContinuity/SDPTrace.lean#L30-L125

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
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterAlignment
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterSlack
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
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
# Real trace duality for Hermitian operators

These finite-dimensional duality lemmas are used to separate the closed
semidefinite slack cone. They do not assume a semidefinite-programming duality
theorem or an optimizer.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Hermitian (H : Type u) [Qudit H] := selfAdjoint (L H)

/-- Cache the canonical real module structure for the trace-duality declarations. -/
 noncomputable instance hermitianRealModule {H : Type u} [Qudit H] :
    Module ℝ (Hermitian H) := inferInstance

variable {H : Type u} [Qudit H] [Nontrivial H]

noncomputable instance hermitianFiniteDimensional : FiniteDimensional ℝ (Hermitian H) :=
  FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (L H)).subtype Subtype.val_injective

/-- Real trace pairing on the real vector space of Hermitian operators. -/
noncomputable def hermitianTracePair : Hermitian H →ₗ[ℝ] Module.Dual ℝ (Hermitian H) where
  toFun X :=
    { toFun := fun Y => (Tr ((X : L H) * (Y : L H))).re
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp [mul_smul_comm] }
  map_add' := by intros; ext; simp [add_mul]
  map_smul' := by intros; ext; simp [smul_mul_assoc]

@[simp] theorem hermitianTracePair_apply (X Y : Hermitian H) :
    hermitianTracePair (H := H) X Y = (Tr ((X : L H) * (Y : L H))).re := rfl

/-- The real trace pairing has no kernel. -/
theorem hermitianTracePair_injective : Function.Injective (hermitianTracePair (H := H)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  have ht : (Tr ((X : L H) * (X : L H))).re = 0 := congrArg (fun f => f X) hX
  have hp : 0 ≤ (X : L H) * (X : L H) := by
    simpa only [X.property.star_eq] using star_mul_self_nonneg (X : L H)
  have hsq : (X : L H) * (X : L H) = 0 := by
    by_contra hn
    exact (ne_of_gt (trace_re_pos_of_ne_zero hp hn)) ht
  apply Subtype.ext
  exact (CStarRing.star_mul_self_eq_zero_iff (X : L H)).mp (by simpa only [X.property.star_eq] using hsq)

/-- Every real linear functional on Hermitian operators is represented by
one Hermitian operator under the trace pairing. -/
theorem hermitianTracePair_surjective : Function.Surjective (hermitianTracePair (H := H)) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    hermitianTracePair_injective
  exact (Subspace.dual_finrank_eq (K := ℝ) (V := Hermitian H)).symm

/-- Positivity can be tested against all positive Hermitian trace partners. -/
theorem hermitian_nonneg_iff_trace (X : Hermitian H) :
    (0 : L H) ≤ X ↔ ∀ Y : Hermitian H, (0 : L H) ≤ Y → 0 ≤ hermitianTracePair (H := H) X Y := by
  constructor
  · intro hX Y hY
    exact trace_product_nonneg hX hY
  · intro h
    apply (LinearMap.nonneg_iff_isPositive _).mpr
    refine ⟨?_, ?_⟩
    · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr X.property
    · intro a
      let Y : Hermitian H := ⟨outer_product a a,
        (outer_product_self_nonneg a).isSelfAdjoint⟩
      have ht := h Y (outer_product_self_nonneg a)
      change 0 ≤ (Tr ((X : L H) * outer_product a a)).re at ht
      rw [show (X : L H) * outer_product a a = outer_product a ((X : L H) a) by
        ext z; simp [outer_product, smul_smul], trace_outer_product] at ht
      change 0 ≤ RCLike.re (inner ℂ a ((X : L H) a)) at ht
      rwa [inner_re_symm] at ht

/-- The real trace as a linear functional on Hermitian operators. -/
noncomputable def hermitianTrace : Hermitian H →ₗ[ℝ] ℝ where
  toFun X := (Tr (X : L H)).re
  map_add' := by intros; simp
  map_smul' := by intros; simp

@[simp] theorem hermitianTrace_apply (X : Hermitian H) :
    hermitianTrace (H := H) X = (Tr (X : L H)).re := rfl

theorem hermitian_smul_nonneg {r : ℝ} (hr : 0 ≤ r) {X : Hermitian H} (hX : 0 ≤ X) :
    0 ≤ r • X := by
  change (0 : L H) ≤ r • (X : L H)
  rw [← algebraMap_smul ℂ r (X : L H)]
  exact smul_nonneg (by exact_mod_cast hr : (0 : ℂ) ≤ (r : ℂ)) hX

theorem hermitian_smul_mono {r : ℝ} (hr : 0 ≤ r) {X Y : Hermitian H} (h : X ≤ Y) :
    r • X ≤ r • Y := by
  apply sub_nonneg.mp
  rw [← smul_sub]
  exact hermitian_smul_nonneg hr (sub_nonneg.mpr h)

theorem hermitianTrace_nonneg {X : Hermitian H} (hX : 0 ≤ X) :
    0 ≤ hermitianTrace (H := H) X := by
  exact ((LinearMap.nonneg_iff_isPositive _).mp hX).trace_nonneg.1

theorem hermitianTrace_mono : Monotone (hermitianTrace (H := H)) := by
  intro X Y h
  have ht := hermitianTrace_nonneg (sub_nonneg.mpr h)
  simpa only [map_sub, sub_nonneg] using ht

theorem hermitian_norm_le_trace {X : Hermitian H} (hX : 0 ≤ X) :
    ‖X‖ ≤ hermitianTrace (H := H) X := norm_le_re_trace hX

end QuantumChannelContinuity


