-- Prove2me | solution 1 for QuantumChannelContinuity.weighted_trace_boundary
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-08T04:14:46.574675+00:00
-- url     : https://prove2.me/submissions/bd25cec3-0d5a-433a-9324-0242d48fa31a

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
import Definitions.Def_CRCD_QuantumChannelContinuity_DivergenceSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_Filter
import Definitions.Def_CRCD_QuantumChannelContinuity_FilterTensor
import Definitions.Def_CRCD_QuantumChannelContinuity_Foundations
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsDiagonal
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsInfiniteLimit
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsMeasurement
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_FoundationsWeakTesting
import Definitions.Def_CRCD_QuantumChannelContinuity_HockeyStick
import Definitions.Def_CRCD_QuantumChannelContinuity_Schatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StabilizedSchatten
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderDuality
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderInterpolation
import Definitions.Def_CRCD_QuantumChannelContinuity_StateOrderPowers
import Definitions.Def_CRCD_QuantumChannelContinuity_StateSupportLimits
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorChannels
import Definitions.Def_CRCD_QuantumChannelContinuity_TensorOrder
import Theorems.Thm_QuantumChannelContinuity_complex_trace_holder_adjoint
import Theorems.Thm_QuantumChannelContinuity_trace_rpow_star_mul_swap

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



















/-- The equivalent non-adjoint trace form, with left Gram operators in both
Schatten factors. -/
private theorem complex_trace_holder [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (A B : L H) :
    ‖Tr (A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have h := complex_trace_holder_adjoint hpq (star A) B
  simpa only [star_star, trace_rpow_star_mul_swap] using h

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/




/-! # Analytic operator powers for weighted Schatten interpolation -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false



private theorem operatorCpow_ofReal {A : L H} (hA : IsStrictlyPositive A) (t : ℝ) :
    operatorCpow A (t : ℂ) = CFC.rpow A t := by
  rw [CFC.rpow_eq_normedSpace_exp_smul_log hA]
  unfold operatorCpow
  rw [Complex.coe_smul]



private theorem operatorCpow_add (A : L H) (z w : ℂ) :
    operatorCpow A (z + w) = operatorCpow A z * operatorCpow A w := by
  letI : NormedAlgebra ℚ (L H) := .restrictScalars ℚ ℂ (L H)
  unfold operatorCpow
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (CFC.log A)).smul_left z).smul_right w)

private theorem star_operatorCpow (A : L H) (z : ℂ) :
    star (operatorCpow A z) = operatorCpow A (star z) := by
  unfold operatorCpow
  have hlog : IsSelfAdjoint (CFC.log A) := cfc_predicate _ _
  rw [NormedSpace.star_exp, star_smul, hlog.star_eq]



private theorem operatorCpow_mul_star {A : L H} (hA : IsStrictlyPositive A) (z : ℂ) :
    operatorCpow A z * star (operatorCpow A z) = CFC.rpow A (2 * z.re) := by
  rw [star_operatorCpow, ← operatorCpow_add, add_comm]
  have hz : star z + z = ((2 * z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp <;> ring
  rw [hz, operatorCpow_ofReal hA]









end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/



/-! # Boundary densities for the analytic interpolation family -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private theorem operatorCpow_unitary_density {X : L H} (hX : IsStrictlyPositive X)
    (U : unitary (L H)) (z : ℂ) :
    (operatorCpow X z * star (U : L H)) * star (operatorCpow X z * star (U : L H)) =
      CFC.rpow X (2 * z.re) := by
  rw [star_mul, star_star, mul_assoc, ← mul_assoc (star (U : L H)), Unitary.coe_star_mul_self,
    one_mul, operatorCpow_mul_star hX]

private theorem mul_operatorCpow_density {σ : L H} (hσ : IsStrictlyPositive σ) (R : L H) (z : ℂ) :
    (R * operatorCpow σ z) * star (R * operatorCpow σ z) =
      R * CFC.rpow σ (2 * z.re) * star R := by
  rw [star_mul, mul_assoc, ← mul_assoc (operatorCpow σ z), operatorCpow_mul_star hσ, mul_assoc]

private theorem mul_operatorCpow_density_eq_re {σ : L H} (hσ : IsStrictlyPositive σ)
    (R : L H) (z : ℂ) :
    (R * operatorCpow σ z) * star (R * operatorCpow σ z) =
      (R * CFC.rpow σ z.re) * star (R * CFC.rpow σ z.re) := by
  rw [mul_operatorCpow_density hσ R z,
    ← operatorCpow_ofReal hσ z.re,
    mul_operatorCpow_density hσ R (z.re : ℂ), Complex.ofReal_re]

/-- Every imaginary boundary translate of the normalized dual power has
Schatten norm exactly one at the conjugate exponent. -/
private theorem normalized_dual_power_trace {X : L H} (hX : IsStrictlyPositive X)
    (hTr : (Tr X).re = 1) (U : unitary (L H)) {q : ℝ} (hq : 1 < q)
    {z : ℂ} (hz : z.re = 1 / q) :
    (Tr (CFC.rpow ((operatorCpow X z * star (U : L H)) *
      star (operatorCpow X z * star (U : L H))) (q / 2))).re ^ (1 / q) = 1 := by
  rw [operatorCpow_unitary_density hX U z, hz]
  have hq0 : 0 < q := by linarith
  have heq : CFC.rpow (CFC.rpow X (2 * (1 / q))) (q / 2) = X := by
    have h := CFC.rpow_rpow X (2 * (1 / q)) (q / 2) (by positivity) hX
    have he : 2 * (1 / q) * (q / 2) = 1 := by field_simp
    rw [he] at h
    exact h.trans (CFC.rpow_one _ hX.nonneg)
  rw [heq, hTr, Real.one_rpow]

end QuantumChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-! # Weighted Schatten interpolation and faithful Rényi order comparisons -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

end QuantumChannelContinuity

open QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open QuantumChannelContinuity in
/-- Hölder gives the exact boundary norm for the holomorphic duality
family; all imaginary powers and the polar unitary are handled explicitly. -/
theorem solution {X σ : L H} (hX : IsStrictlyPositive X)
    (hσ : IsStrictlyPositive σ) (hTr : (Tr X).re = 1) (U : unitary (L H)) (R : L H)
    {p : ℝ} (hp : 1 < p) {z w : ℂ} (hz : z.re = 1 - 1 / p)
    (hw : w.re = 1 / p - 1 / 2) :
    ‖Tr (operatorCpow X z * star (U : L H) * R * operatorCpow σ w)‖ ≤
      schattenNorm (R * CFC.rpow σ (1 / p - 1 / 2)) p := by
  let q := p / (p - 1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hzq : z.re = 1 / q := by
    rw [hz]
    simpa only [one_div] using hpq.one_sub_inv
  have h := complex_trace_holder hpq.symm
    (operatorCpow X z * star (U : L H)) (R * operatorCpow σ w)
  have hnorm := normalized_dual_power_trace hX hTr U (q := q) (z := z) hpq.symm.lt hzq
  rw [hnorm, one_mul,
    mul_operatorCpow_density_eq_re hσ R w, hw] at h
  have hswap := trace_rpow_star_mul_swap (R * CFC.rpow σ (1 / p - 1 / 2)) (p / 2)
  simpa only [schattenNorm, schattenWeight, hswap, mul_assoc] using h

end
