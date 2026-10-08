-- Prove2me | solution 1 for QuantumChannelContinuity.exists_faithful_schatten_dual
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T03:38:09.751992+00:00
-- url     : https://prove2.me/submissions/5035246a-68fd-43e2-ab90-8018fe012a64

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Hadamard
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
import Mathlib.Topology.UniformSpace.HeineCantor
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
import Definitions.Def_CRCD_QuantumChannelContinuity_Channels
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderDuality
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Theorems.Thm_QuantumChannelContinuity_exists_right_polar_unitary

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-! # Faithful polar witnesses for Schatten duality -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private theorem star_mul_self_strictlyPositive {C : L H} (hC : IsUnit C) :
    IsStrictlyPositive (star C * C) :=
  ⟨star_mul_self_nonneg _, hC.star.mul hC⟩







private theorem schattenWeight_pos {C : L H} (hC : IsUnit C) (p : ℝ) :
    0 < schattenWeight C p := by
  have hp : IsStrictlyPositive (CFC.rpow (star C * C) (p / 2)) :=
    IsStrictlyPositive.rpow (star C * C) (p / 2) (star_mul_self_strictlyPositive hC)
  exact trace_re_pos_of_ne_zero hp.nonneg hp.isUnit.ne_zero



/-- Trace scaling written over the real scalar field. -/
private theorem real_trace_smul (r : ℝ) (A : L H) : (Tr (r • A)).re = r * (Tr A).re := by
  rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

end QuantumChannelContinuity

open QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open QuantumChannelContinuity in
/-- The positive normalized dual density and its polar unitary attain the
Schatten dual pairing on every faithful matrix. -/
theorem solution {C : L H} (hC : IsUnit C) {p : ℝ} (hp : 1 < p) :
    ∃ (X : L H) (U : unitary (L H)), IsStrictlyPositive X ∧ (Tr X).re = 1 ∧
      ‖Tr (CFC.rpow X (1 - 1 / p) * star (U : QuantumState.L H) * C)‖ = schattenNorm C p := by
  let L := star C * C
  let Z := schattenWeight C p
  let A := CFC.rpow L (p / 2)
  let X := Z⁻¹ • A
  have hL : IsStrictlyPositive L := star_mul_self_strictlyPositive hC
  have hA : IsStrictlyPositive A := IsStrictlyPositive.rpow L (p / 2) hL
  have hZ : 0 < Z := schattenWeight_pos hC p
  have hp0 : 0 < p := by linarith
  have hX : IsStrictlyPositive X := IsStrictlyPositive.smul (inv_pos.mpr hZ) hA
  obtain ⟨U, hU⟩ := exists_right_polar_unitary hC
  refine ⟨X, U, hX, ?_, ?_⟩
  · change (Tr (Z⁻¹ • A)).re = 1
    rw [real_trace_smul]
    change Z⁻¹ * Z = 1
    exact inv_mul_cancel₀ hZ.ne'
  · have hpow : CFC.rpow X (1 - 1 / p) =
        (Z⁻¹) ^ (1 - 1 / p) • CFC.rpow L ((p / 2) * (1 - 1 / p)) := by
      change CFC.rpow (Z⁻¹ • A) (1 - 1 / p) = _
      calc
        _ = (Z⁻¹) ^ (1 - 1 / p) • CFC.rpow A (1 - 1 / p) :=
          operator_rpow_smul A ((LinearMap.nonneg_iff_isPositive A).mp hA.nonneg)
            (inv_nonneg.mpr hZ.le) (1 - 1 / p)
        _ = _ := by
          congr 1
          exact CFC.rpow_rpow L (p / 2) (1 - 1 / p) (by positivity) hL
    have hprod : CFC.rpow X (1 - 1 / p) * star (U : QuantumState.L H) * C =
        (Z⁻¹) ^ (1 - 1 / p) • A := by
      rw [mul_assoc, hU, hpow, smul_mul_assoc]
      congr 1
      calc
        _ = CFC.rpow L ((p / 2) * (1 - 1 / p) + 1 / 2) := (CFC.rpow_add hL.isUnit).symm
        _ = A := by congr 1; field_simp; ring
    have hscalar : (Z⁻¹) ^ (1 - 1 / p) * Z = Z ^ (1 / p) := by
      calc
        _ = Z ^ (-(1 - 1 / p)) * Z ^ (1 : ℝ) := by
          rw [Real.rpow_one, Real.rpow_neg hZ.le, Real.inv_rpow hZ.le]
        _ = Z ^ (-(1 - 1 / p) + 1) := (Real.rpow_add hZ _ _).symm
        _ = Z ^ (1 / p) := by congr 1; ring
    have hpos : 0 ≤ Tr ((Z⁻¹) ^ (1 - 1 / p) • A) :=
      ((LinearMap.nonneg_iff_isPositive _).mp
        (smul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hZ.le) _) hA.nonneg)).trace_nonneg
    have hnorm : ‖Tr ((Z⁻¹) ^ (1 - 1 / p) • A)‖ = (Tr ((Z⁻¹) ^ (1 - 1 / p) • A)).re := by
      simpa only [Complex.ofReal_re] using (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hpos)).symm
    rw [hprod, hnorm, real_trace_smul]
    exact hscalar

end
