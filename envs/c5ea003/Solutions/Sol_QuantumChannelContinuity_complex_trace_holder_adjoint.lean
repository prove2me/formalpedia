-- Prove2me | solution 1 for QuantumChannelContinuity.complex_trace_holder_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:04:35.015883+00:00
-- url     : https://prove2.me/submissions/08c58a99-0f2f-4654-a477-2b69ee622b5a

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
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Theorems.Thm_QuantumChannelContinuity_complex_trace_holder_lt_two

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-!
# Complex trace Hölder

The bound is proved from Hilbert–Schmidt Cauchy–Schwarz and the already
proved positive-operator trace Hölder inequality. Positive regularization
handles all singular operators.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder MatrixOrder NNReal Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {H : Type u} [Qudit H]

/-- Hilbert–Schmidt coordinates represent the full complex trace pairing. -/
private theorem coefficientVector_inner (A B : L H) :
    inner ℂ (coefficientVector A) (coefficientVector B) = Tr (star A * B) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H)]
  simp only [coefficientVector, PiLp.inner_apply,
    LinearMap.star_eq_adjoint, Module.End.mul_apply, LinearMap.adjoint_inner_right]

private theorem complex_trace_hilbertSchmidt (A B : L H) :
    ‖Tr (star A * B)‖ ≤ Real.sqrt (Tr (A * star A)).re * Real.sqrt (Tr (B * star B)).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (coefficientVector A) (coefficientVector B)
  rw [coefficientVector_inner] at h
  have hn (C : L H) : Real.sqrt (Tr (C * star C)).re = ‖coefficientVector C‖ := by
    change Real.sqrt (Tr (coefficientDensity C)).re = _
    rw [← coefficientVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn] using h













end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
universe u
variable {H : Type u} [Qudit H]
open QuantumChannelContinuity in
/-- Complex trace Hölder for arbitrary operators with conjugate exponents.
No support, invertibility, or positivity assumptions on the operators occur. -/
theorem solution [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (A B : L H) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  rcases lt_trichotomy p 2 with hp | hp | hp
  · exact complex_trace_holder_lt_two hpq hp A B
  · have hq : q = 2 := by rw [hpq.conjugate_eq, hp]; norm_num
    subst p
    subst q
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), CFC.rpow_eq_pow,
      CFC.rpow_one _ (mul_star_self_nonneg A), CFC.rpow_one _ (mul_star_self_nonneg B),
      Real.sqrt_eq_rpow] using complex_trace_hilbertSchmidt A B
  · have hq : q < 2 := by
      rw [hpq.conjugate_eq]
      apply (div_lt_iff₀ hpq.sub_one_pos).2
      linarith
    have h := complex_trace_holder_lt_two hpq.symm hq B A
    have hsymm : ‖Tr (star B * A)‖ = ‖Tr (star A * B)‖ := by
      rw [← coefficientVector_inner, ← coefficientVector_inner]
      exact norm_inner_symm _ _
    simpa only [hsymm, mul_comm] using h

end
