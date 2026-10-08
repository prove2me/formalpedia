-- Prove2me | solution 1 for QuantumChannelContinuity.complex_trace_holder_majorant
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T03:49:23.937504+00:00
-- url     : https://prove2.me/submissions/b14c261b-b362-47bb-9950-c563ef25ba9e

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







private theorem holder_weight_sqrt {p q R S : ℝ} (hpq : p.HolderConjugate q)
    (hp2 : p < 2) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Real.sqrt R * Real.sqrt (R ^ ((2 - p) / p) * S ^ (2 / q)) =
      R ^ (1 / p) * S ^ (1 / q) := by
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have h2p : 0 ≤ 2 - p := by linarith
  rw [Real.sqrt_mul (Real.rpow_nonneg hR _), Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hR, ← Real.rpow_mul hS, ← mul_assoc,
    ← Real.rpow_add_of_nonneg hR (by positivity) (by positivity)]
  congr 1
  · congr 1
    field_simp
    ring
  · congr 1
    ring

end QuantumChannelContinuity

open QuantumChannelContinuity
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
universe u
variable {H : Type u} [Qudit H]
open QuantumChannelContinuity in
/-- Weighted Hilbert–Schmidt proves Hölder below exponent two with any
positive-definite majorant of the left Gram operator. -/
theorem solution [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (A B X : L H)
    (hX : X ∈ pdSetLM) (hAX : A * star A ≤ X) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow X (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have hp := hpq.lt
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have h2p : 0 < 2 - p := by linarith
  have hX0 := nonneg_of_pdSetLM hX
  have hXp := (LinearMap.nonneg_iff_isPositive _).1 hX0
  have hXu := isUnit_of_pdSetLM hX
  let a := (p - 2) / 4
  let S := CFC.rpow X a
  let T := CFC.rpow X (-a)
  let C := S * A
  let D := T * B
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hT : T.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hSstar : star S = S := hS.isSelfAdjoint.star_eq
  have hTstar : star T = T := hT.isSelfAdjoint.star_eq
  have hST : S * T = 1 := by
    change X ^ a * X ^ (-a) = 1
    rw [← CFC.rpow_add hXu, add_neg_cancel, CFC.rpow_zero X hX0]
  have hpair : star C * D = star A * B := by
    dsimp [C, D]
    rw [star_mul, hSstar]
    calc
      star A * S * (T * B) = star A * (S * T) * B := by noncomm_ring
      _ = star A * B := by rw [hST, mul_one]
  have hSX : S * X * S = CFC.rpow X (p / 2) := by
    change CFC.rpow X a * X * CFC.rpow X a = _
    conv_lhs => arg 1; arg 2; rw [← CFC.rpow_one X hX0]
    change CFC.rpow X a * CFC.rpow X 1 * CFC.rpow X a = _
    rw [operator_rpow_mul X hXp a 1 (by dsimp [a]; linarith : a + 1 ≠ 0),
      operator_rpow_mul X hXp (a + 1) a (by dsimp [a]; linarith : a + 1 + a ≠ 0)]
    congr 1
    dsimp [a]
    ring
  have hCeq : C * star C = S * (A * star A) * S := by
    simp only [C, star_mul, hSstar]
    noncomm_ring
  have hCbound : (Tr (C * star C)).re ≤ (Tr (CFC.rpow X (p / 2))).re := by
    have h := trace_mul_re_mono (hS.isSelfAdjoint.conjugate_le_conjugate hAX)
      (1 : L H) LinearMap.isPositive_one
    simpa only [mul_one, ← hCeq, hSX] using h
  have hTT : T * T = CFC.rpow X ((2 - p) / 2) := by
    change CFC.rpow X (-a) * CFC.rpow X (-a) = _
    rw [operator_rpow_mul X hXp (-a) (-a) (by dsimp [a]; linarith : -a + -a ≠ 0)]
    congr 1
    dsimp [a]
    ring
  have hDtrace : Tr (D * star D) = Tr (CFC.rpow X ((2 - p) / 2) * (B * star B)) := by
    have heq : D * star D = (T * (B * star B)) * T := by
      simp only [D, star_mul, hTstar]
      noncomm_ring
    rw [heq, LinearMap.trace_mul_comm ℂ (T * (B * star B)) T, ← mul_assoc, hTT]
  have hrs : (p / (2 - p)).HolderConjugate (q / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · apply (lt_div_iff₀ h2p).2
      linarith
    · have hh := hpq.inv_add_inv_eq_one
      field_simp at hh ⊢
      nlinarith [hpq.mul_eq_add]
  have hD := trace_holder hrs (CFC.rpow X ((2 - p) / 2)) (B * star B)
    ((LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg)
    ((LinearMap.nonneg_iff_isPositive _).1 (mul_star_self_nonneg B))
  have hpow : CFC.rpow (CFC.rpow X ((2 - p) / 2)) (p / (2 - p)) = CFC.rpow X (p / 2) := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X ((2 - p) / 2) (p / (2 - p))
      (by positivity) (by positivity) hX0]
    congr 1
    field_simp
  rw [hpow] at hD
  have hr : 1 / (p / (2 - p)) = (2 - p) / p := by field_simp
  have hs : 1 / (q / 2) = 2 / q := by field_simp
  rw [hr, hs] at hD
  have h := complex_trace_hilbertSchmidt C D
  rw [hpair, hDtrace] at h
  refine h.trans ((mul_le_mul (Real.sqrt_le_sqrt hCbound) (Real.sqrt_le_sqrt hD)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq ?_)
  exact _root_.QuantumChannelContinuity.holder_weight_sqrt hpq hp2 (trace_rpow_re_nonneg X (p / 2))
    (trace_rpow_re_nonneg (B * star B) (q / 2))

end
